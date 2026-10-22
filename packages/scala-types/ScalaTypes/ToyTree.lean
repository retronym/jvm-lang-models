import ScalaTypes.ToyKernel
import Query.Revision
import Query.Interp
/-!
# The toy's trees: node identity, typed forms as facts, targeting, the session, revisions

Track I's targeting and incrementality are about trees ([track-i.md §6](../../scala/docs/track-i.md)),
which the namer ([`ToyNamer.rulesOf`](ToyNamer.lean)) and the kernel ([`ToyKernel`](ToyKernel.lean))
do not have: a request's target is a position, an edit is a replacement, and what survives an edit
is a question of identity. This file is the smallest tree that carries those three.

* A **green tree with identity**: the unit is a list of declaration nodes, each with its member
  nodes, every node with an id; an `Edit` replaces, inserts or deletes a declaration or replaces one
  member, and the nodes it does not touch keep their ids (Wagner and Graham's reuse, without the
  parsing). Positions are paths (declaration index, member index), not offsets.
* **Typed forms as facts**: `typedMember` (the member's type, and its body typed against a declared
  type) and `typedDecl` (the body list with synthetics, as [`unitAnswer`](ToyKernel.lean) prints it)
  are facts keyed by node id whose rules ask the namer's facts. The unit's typed tree is the store
  restricted to these, filled on demand: no `typeUnit` loop, no consumed map.
* **Targeting** is then demand: a request at a path forces the typed fact at that node and what it
  asks, nothing else, and answers as the whole-tree check does (`targeted_eq_whole`).
* **The session** is the store: successive requests on one revision answer as each would on a
  fresh store (`session_eq_fresh_toy`), with the work of the second and later ones gone.
* **Revisions**: an edit's footprint says which rules it may have changed (the node's own facts,
  and the facts that read the edited name other than through a fact); everything else is
  re-validated by trace ([`Query.Revision.reval`](../../query/Query/Revision.lean)). The three tiers
  of invalidation are theorems on an example each.
-/

namespace ScalaTypes.ToyTree

open Query Query.Lazy Query.Interrupt Query.Revision ScalaTypes.ToyNamer

/-! ## The green tree -/

structure MemberNode where
  id : Nat
  m : Member
  deriving DecidableEq, Repr

/-- A declaration node: its header (`stats` unused; the members are the nodes) and its members. -/
structure DeclNode where
  id : Nat
  head : Decl
  members : List MemberNode
  deriving DecidableEq, Repr

/-- The unit: top-level declaration nodes, and the next free id. -/
structure Tree where
  decls : List DeclNode
  next : Nat
  deriving DecidableEq, Repr

def DeclNode.toDecl (d : DeclNode) : Decl := { d.head with stats := d.members.map (.member ·.m) }

def DeclNode.ref (d : DeclNode) : Ref := if d.head.obj then obj d.head.name else cls d.head.name

def Tree.program (t : Tree) : Program := t.decls.map DeclNode.toDecl

/-- A new declaration node with fresh ids for it and its members. -/
def newDecl (d : Decl) (next : Nat) : DeclNode × Nat :=
  let ms := d.members
  (⟨next, { d with stats := [] }, ms.zipIdx.map fun (m, i) => ⟨next + 1 + i, m⟩⟩, next + 1 + ms.length)

def Tree.ofProgram (p : Program) : Tree :=
  p.foldl (fun t d => let (n, next) := newDecl d t.next; ⟨t.decls ++ [n], next⟩) ⟨[], 0⟩

/-- A position: a declaration, or a member of one, by index. -/
inductive Path
  | decl (i : Nat)
  | member (i j : Nat)
  deriving DecidableEq, Repr

/-- A tree replacement. -/
inductive Edit
  | replaceDecl (i : Nat) (d : Decl)
  | insertDecl (i : Nat) (d : Decl)
  | deleteDecl (i : Nat)
  | replaceMember (i j : Nat) (m : Member)
  deriving DecidableEq, Repr

def setAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, y => y :: xs
  | x :: xs, n + 1, y => x :: setAt xs n y

def insertAt {α : Type} : List α → Nat → α → List α
  | xs, 0, y => y :: xs
  | [], _, y => [y]
  | x :: xs, n + 1, y => x :: insertAt xs n y

def removeAt {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, n + 1 => x :: removeAt xs n

/-- Apply an edit: the replaced or inserted nodes are new, every other node keeps its id. -/
def Tree.apply (t : Tree) : Edit → Tree
  | .replaceDecl i d => let (n, next) := newDecl d t.next; ⟨setAt t.decls i n, next⟩
  | .insertDecl i d => let (n, next) := newDecl d t.next; ⟨insertAt t.decls i n, next⟩
  | .deleteDecl i => ⟨removeAt t.decls i, t.next⟩
  | .replaceMember i j m =>
    match t.decls[i]? with
    | none => t
    | some d => ⟨setAt t.decls i { d with members := setAt d.members j ⟨t.next, m⟩ }, t.next + 1⟩

def Tree.nodeAt (t : Tree) : Path → Option Nat
  | .decl i => (t.decls[i]?).map (·.id)
  | .member i j => (t.decls[i]?).bind fun d => (d.members[j]?).map (·.id)

def Tree.paths (t : Tree) : List Path :=
  t.decls.zipIdx.flatMap fun (d, i) => Path.decl i :: d.members.zipIdx.map fun (_, j) => Path.member i j

def findDeclNode (t : Tree) (id : Nat) : Option DeclNode := t.decls.find? (·.id == id)

def findMemberNode (t : Tree) (id : Nat) : Option (DeclNode × MemberNode) :=
  t.decls.findSome? fun d => (d.members.find? (·.id == id)).map (d, ·)

/-! ## Typed forms as facts -/

inductive TFact
  | namer (f : Fact)
  | typedDecl (id : Nat)
  | typedMember (id : Nat)
  deriving DecidableEq, Repr

inductive TValue
  /-- A namer fact's value. -/
  | v (x : Value)
  /-- A typed member: its type (the namer's), and its body typed against a declared type. -/
  | member (sig : Value) (body : Option Value)
  /-- A typed declaration: each body (the declaration's, and a case class's synthetic companion's)
  as a sorted list of member and type. -/
  | bodies (bs : List (String × List (String × Value)))
  deriving DecidableEq, Repr

def TValue.toValue : TValue → Value
  | .v x => x
  | _ => .err "not a value"

abbrev TRule (α : Type) := Task TFact (fun _ => TValue) α

/-- A namer rule, asking its facts through the tree's facts. Peeks are read as forces: the cuts
used here (`fine`, `scalac`) never peek. -/
def lift (t : Rule Value) : TRule Value :=
  t.rename (fun pr => TFact.namer (fact pr)) (fun _ tv => tv.toValue)

def askNamer (f : Fact) : TRule Value := .ask (.namer f) fun tv => .pure tv.toValue

def memberTypes (r : Ref) : List String → TRule (List (String × Value))
  | [] => pure []
  | n :: ns => do
    let v ← askNamer (.mem r n)
    let rest ← memberTypes r ns
    pure ((n, v) :: rest)

/-- The body of `r` as `unitAnswer` prints it: its member names with synthetics, sorted, each with
its type. -/
def bodyOf (r : Ref) : TRule (List (String × Value)) := do
  let v ← askNamer (.decls r)
  match v with
  | .names ns => memberTypes r (ToyKernel.sortedSet ns)
  | other => pure [("<decls>", other)]

/-- The rules of the tree's facts: the namer's as they are; a member's typed form asks its type
and, when the type is declared and there is a body, types the body; a declaration's typed form
asks its member set and each member's type, and its synthetic companion's when it has no
companion of its own. -/
def rulesOf (cut : Cut) (t : Tree) : Rules TFact TValue
  | .namer f => (lift (ToyNamer.rulesOf cut t.program f)).bind fun v => pure (.v v)
  | .typedMember id =>
    match findMemberNode t id with
    | none => pure (.v (.err "no such node"))
    | some (d, m) => do
      let sig ← askNamer (.mem d.ref m.m.name)
      if m.m.declared.isSome && !m.m.path.isEmpty then
        let body ← lift (typePath cut t.program d.ref m.m.path)
        pure (.member sig (some body))
      else pure (.member sig none)
  | .typedDecl id =>
    match findDeclNode t id with
    | none => pure (.v (.err "no such node"))
    | some d => do
      let b ← bodyOf d.ref
      let hasCompanion := t.decls.any fun o => o.head.obj && o.head.name == d.head.name
      if d.head.isCase && !d.head.obj && !hasCompanion then
        let cb ← bodyOf (obj d.head.name)
        pure (.bodies [(ToyKernel.bodyKey d.toDecl, b), (s!"object {d.head.name} (synthetic)", cb)])
      else pure (.bodies [(ToyKernel.bodyKey d.toDecl, b)])

/-- The facts of a tree: the namer's for each declaration (and a case class's synthetic
companion), and the typed forms of each node. -/
def facts (t : Tree) : List TFact :=
  let p := t.program
  t.decls.flatMap fun d =>
    let r := d.ref
    let namerOf (r : Ref) : List TFact :=
      [.namer (.decls r), .namer (.info r)] ++ (ownNames p r).map (TFact.namer <| .mem r ·)
    let companion :=
      if d.head.isCase && !d.head.obj && !(t.decls.any fun o => o.head.obj && o.head.name == d.head.name)
      then namerOf (obj d.head.name) else []
    namerOf r ++ companion ++ [.typedDecl d.id] ++ d.members.map (.typedMember ·.id)

def fuel : Nat := 60

/-- The request at a path: the typed form of the node there. -/
def request (t : Tree) : Path → Option TFact
  | .decl i => (t.nodeAt (.decl i)).map .typedDecl
  | .member i j => (t.nodeAt (.member i j)).map .typedMember

def requests (t : Tree) : List TFact := t.paths.filterMap (request t)

/-! ## Targeting -/

/-- A targeted request: the fact at the node, from an empty store. -/
def targeted (cut : Cut) (t : Tree) (q : TFact) : Out TFact TValue × Memo TFact TValue :=
  reval (rulesOf cut t) (fun _ => false) empty 0 fuel [] empty q

/-- The whole-tree check: every node's typed form, in order. -/
def whole (cut : Cut) (t : Tree) : Memo TFact TValue :=
  (fresh (rulesOf cut t) 0 fuel (requests t)).2

/-- The answer the whole-tree check gives a request: served from its store. -/
def afterWhole (cut : Cut) (t : Tree) (q : TFact) : Out TFact TValue :=
  (reval (rulesOf cut t) (fun _ => false) empty 0 fuel [] (whole cut t) q).1

/-- Every request at every path answers as it does after the whole-tree check. -/
def targetedEqWhole (cut : Cut) (t : Tree) : Bool :=
  (requests t).all fun q => (targeted cut t q).1 == afterWhole cut t q

/-- The targeted request's store is within the whole check's. -/
def targetedWithinWhole (cut : Cut) (t : Tree) : Bool :=
  (requests t).all fun q =>
    (facts t).all fun f => match (targeted cut t q).2 f, whole cut t f with
      | some e, some e' => e.value == e'.value
      | some _, none => false
      | none, _ => true

/-- The work of a targeted request: the facts it computed. -/
def targetedWork (cut : Cut) (t : Tree) (q : TFact) : Nat :=
  (computedAt (targeted cut t q).2 0 (facts t)).length

def wholeWork (cut : Cut) (t : Tree) : Nat := (computedAt (whole cut t) 0 (facts t)).length

/-! ## Revisions -/

/-- A revision: the tree, its store, its number. -/
structure Rev where
  tree : Tree
  memo : Memo TFact TValue
  rev : Nat

def Rev.ofProgram (p : Program) : Rev := ⟨Tree.ofProgram p, empty, 0⟩
def Rev.ofProgram' (t : Tree) : Rev := ⟨t, empty, 0⟩

/-- Serve a request on the revision, keeping the store (the session). -/
def Rev.ask (cut : Cut) (r : Rev) (q : TFact) : Out TFact TValue × Rev :=
  let (o, m) := reval (rulesOf cut r.tree) (fun _ => false) empty r.rev fuel [] r.memo q
  (o, { r with memo := m })

def Rev.askAll (cut : Cut) (r : Rev) (qs : List TFact) : List (Out TFact TValue) × Rev :=
  let (os, m) := revalAll (rulesOf cut r.tree) (fun _ => false) empty r.rev fuel qs r.memo
  (os, { r with memo := m })

/-- Does the member read a name other than through a fact: as its declared type (a class of the
program or not), or as the first step of its path (a top-level object)? -/
def memberReads (m : Member) (names : List String) : Bool :=
  m.declared.any (· ∈ names) || m.path.head?.any (· ∈ names)

/-- The facts a declaration's replacement, insertion or removal may change the rules of: the
declaration's own facts under both names; the member types that read either name directly, or
walk a path at all when an implicit class comes or goes (`findImplicit` scans the headers); the
typed forms of the declaration and of a declaration of either name (a case class's typed form
reads whether it has a companion). -/
def declFootprint (t : Tree) (ids : List Nat) (names : List String) (implicit : Bool) : TFact → Bool
  | .namer (.decls r) => r.name ∈ names
  | .namer (.info r) => r.name ∈ names
  | .namer (.mem r n) =>
    r.name ∈ names ||
    (match findDecl t.program r with
      | some d =>
        (d.params.find? (·.1 == n)).any (·.2 ∈ names) ||
        (d.members.find? (·.name == n)).any fun m => memberReads m names || (implicit && !m.path.isEmpty)
      | none => false)
  | .typedDecl id => id ∈ ids || t.next ≤ id || (findDeclNode t id).any (·.head.name ∈ names)
  | .typedMember id => t.next ≤ id || (findMemberNode t id).any (·.1.id ∈ ids)

/-- The footprint of an edit: which facts' rules it may have changed. A member's replacement
touches its owner's member set and the type under its old and new names, and its own typed form;
a change of its deprecation touches every member type (`step` reads the flag directly). -/
def footprint (t : Tree) : Edit → TFact → Bool
  | .replaceDecl i d => fun q =>
    match t.decls[i]? with
    | some old => declFootprint t [old.id] [old.head.name, d.name] (old.head.isImplicit || d.isImplicit) q
    | none => false
  | .insertDecl _ d => declFootprint t [] [d.name] d.isImplicit
  | .deleteDecl i => fun q =>
    match t.decls[i]? with
    | some old => declFootprint t [old.id] [old.head.name] old.head.isImplicit q
    | none => false
  | .replaceMember i j m => fun q =>
    match t.decls[i]? >>= fun d => (d.members[j]?).map (d, ·) with
    | some (d, old) =>
      let r := d.ref
      match q with
      | .namer (.decls r') => r' == r
      | .namer (.mem r' n) => (r' == r && (n == old.m.name || n == m.name)) || old.m.deprecated != m.deprecated
      | .typedMember id => id == old.id || id == t.next || old.m.deprecated != m.deprecated
      | _ => false
    | none => false

/-- Apply an edit: the next revision, every fact of the new tree re-validated. -/
def Rev.edit (cut : Cut) (r : Rev) (e : Edit) : Rev :=
  let t' := r.tree.apply e
  let m' := (revalAll (rulesOf cut t') (fun q => !footprint r.tree e q) r.memo (r.rev + 1) fuel (facts t') empty).2
  ⟨t', m', r.rev + 1⟩

/-- Every fact of the revision demanded: the whole unit typed. -/
def Rev.validateAll (cut : Cut) (r : Rev) : Rev := (r.askAll cut (facts r.tree)).2

/-- The revision's store agrees with a fresh run of its rules on every fact: the check of a
footprint on an example. -/
def Rev.agreesWithFresh (cut : Cut) (r : Rev) : Bool :=
  let f := (fresh (rulesOf cut r.tree) r.rev fuel (facts r.tree)).2
  (facts r.tree).all fun q => (r.memo q).map (·.value) == (f q).map (·.value)

/-- `Same` checked on an example: for every fact of the new tree outside the footprint, the old
rule under the new store gives the new rule's value and asks the same facts. -/
def sameOk (cut : Cut) (t : Tree) (e : Edit) : Bool :=
  let t' := t.apply e
  let m := (fresh (rulesOf cut t') 0 fuel (facts t')).2
  let ρ : TFact → TValue := fun q => ((m q).map (·.value)).getD (.v absent)
  (facts t').all fun q => footprint t e q ||
    ((rulesOf cut t q).run ρ == (rulesOf cut t' q).run ρ && (rulesOf cut t q).trace ρ == (rulesOf cut t' q).trace ρ)

/-- The facts whose values the revision changed. -/
def Rev.changed (r : Rev) : List TFact := changedAt r.memo r.rev (facts r.tree)
/-- The facts whose rules the revision ran: its work. -/
def Rev.computed (r : Rev) : List TFact := computedAt r.memo r.rev (facts r.tree)
/-- The facts the revision reused from the one before, re-validated by trace. -/
def Rev.reused (r : Rev) : List TFact :=
  (facts r.tree).filter fun q => match r.memo q with | some e => e.computed < r.rev | none => false

/-! ## Witnesses: targeting and the session on the kernel's scenarios -/

/-- The programs of the Java toy's scenarios (a two-unit scenario as one unit). -/
def programs : List Program := ToyKernel.scenarios.map fun sc => sc.units.flatMap (·.2)

/-- **Targeting is demand.** On every scenario, under the fine and the scalac cut, a request at any
path answers from an empty store as it does from the whole-tree check's store, and stores only
facts the whole check stores, with the same values. Nothing a typed form reads is typer-only state
here (the synthetics are the namer's), so the I5 shape (a completion served before the class is
typed sees the namer's members) cannot arise: the equality holds at every path.

This is also the statement that **I13 cannot happen once the burst is a fact**. In the kernel the
case class's `equals`, `hashCode` and `toString` reach the class's scope as a side effect of typing
its template (`ToyKernel.finishMethodSynthesis` writes `scopeSynth`, which `memberNamesK` reads);
here every fact a typed form relies on is a rule of `rulesOf` (the synthetics are in
`ToyNamer.ownNames`, so `decls` of the class has them whoever asks), and a request forces exactly
what it relies on. The contrast, the kernel with a target that skips its siblings, is
`i13_burst_side_effect` below. -/
theorem targeted_eq_whole :
    ∀ p ∈ programs, ∀ cut ∈ [Cut.fine, .scalac],
      targetedEqWhole cut (Tree.ofProgram p) = true ∧ targetedWithinWhole cut (Tree.ofProgram p) = true := by
  decide

/-- The work of each request on `case-class-completion`, against the whole check's: a completion
at `Use.f` computes 6 facts of the unit's 20. -/
theorem targeted_work_caseToy :
    (requests (Tree.ofProgram caseToy)).map (targetedWork .scalac (Tree.ofProgram caseToy)) = [2, 11, 2, 6, 2, 6] ∧
    wholeWork .scalac (Tree.ofProgram caseToy) = 20 := by
  decide

/-! ## Witness: I13, the burst as a side effect against the burst as a fact -/

/-- A completion at a path, by demand: the typed form of the member there, then the member set of
its type, on one store. -/
def completionAt (cut : Cut) (t : Tree) (path : Path) : Option (String × List String) :=
  match request t path with
  | none => none
  | some q =>
    let (o, r) := (Rev.ofProgram' t).ask cut q
    match o with
    | .ok (.member (.typed ty) _) =>
      match ty.ty with
      | .ref c =>
        match (r.ask cut (.namer (.decls c))).1 with
        | .ok (.v (.names ns)) => some (c.name, ToyKernel.sortedSet ns)
        | _ => none
      | _ => none
    | _ => none

/-- The kernel's completion with a target that skips its siblings (the dotc spike's targeting):
only the declaration enclosing the target is typed, so no other template's burst runs. -/
def kernelSkipping (sc : ToyKernel.Scenario) (f : String) (t : ToyKernel.Target) : ToyKernel.Answer :=
  let m : ToyKernel.K ToyKernel.Answer := do
    ToyKernel.newRun sc.units
    let some u ← ToyKernel.getUnit f | return .text "<no such file>"
    modify fun st => { st with target := some t }
    let r ← tryCatch (do
        for (d, pos) in u.decls.zipIdx do
          if d.name == t.decl then
            let _ ← ToyKernel.typeDecl (ToyKernel.serve 3) ToyKernel.pollForWork f d pos []
        pure none) (fun e => pure (some e))
    match r with
    | some (.typerResult a) => return a
    | _ => return .text "<target not reached>"
  match (m.run.run (ToyKernel.fresh .before sc none)).1 with
  | .ok a => a
  | .error _ => .text "<cancelled>"

/-- The kernel's completion as scalac serves it on a fresh run: a targeted check that types the
unit in order up to the target, so the template of `L` (and its burst) comes first. -/
def kernelInOrder (sc : ToyKernel.Scenario) (f : String) (t : ToyKernel.Target) : ToyKernel.Answer :=
  let m : ToyKernel.K ToyKernel.Answer := do
    ToyKernel.newRun sc.units
    ToyKernel.serve 3 (.completion f t.decl t.member)
  match (m.run.run (ToyKernel.fresh .before sc none)).1 with
  | .ok a => a
  | .error _ => .text "<cancelled>"

/-- **I13 on `case-class-completion`**: the completion at `Use.f` (whose type is the case class
`L`). Targeted by demand over the tree's facts, it has `L`'s synthetics, as the kernel's in-order
check does; the kernel with a target that skips the sibling `L` has only the members that do not
come from the burst (`copy` is the namer's synthetic tree, entered with the class), since
`equals`, `hashCode` and `toString` are entered when `L`'s template is typed. -/
theorem i13_burst_side_effect :
    completionAt .scalac (Tree.ofProgram caseToy) (.member 2 1) =
      some ("L", ["a", "copy", "equals", "hashCode", "self", "toString"]) ∧
    kernelInOrder ToyKernel.caseClassCompletion "A" ⟨"Use", "f"⟩ =
      .completion "L" ["a", "copy", "equals", "hashCode", "self", "toString"] ∧
    kernelSkipping ToyKernel.caseClassCompletion "A" ⟨"Use", "f"⟩ = .completion "L" ["a", "copy", "self"] := by
  decide +kernel

/-- A session's answers against each request alone on a fresh store. -/
def sessionEqFresh (cut : Cut) (t : Tree) (qs : List TFact) : Bool :=
  ((Rev.ofProgram' t).askAll cut qs).1 == qs.map fun q => (targeted cut t q).1

/-- **The session is a fresh run, request for request**, on every scenario, every path in order
and in reverse: [`Query.Revision.session_eq_fresh`](../../query/Query/Revision.lean) on the ranked
programs, and the same by `decide` on `cycle`, which is not ranked. -/
theorem session_eq_fresh_toy :
    ∀ p ∈ programs, sessionEqFresh .scalac (Tree.ofProgram p) (requests (Tree.ofProgram p)) = true ∧
      sessionEqFresh .scalac (Tree.ofProgram p) (requests (Tree.ofProgram p)).reverse = true := by
  decide

/-! ## Witnesses: the three tiers of invalidation -/

/-- `C.q` has a declared type and a body; `p` and `s` read it. -/
def tier1 : Program := [int,
  { name := "C", stats := [ToyKernel.m "c" "Int", .member { name := "q", declared := some "C", path := ["c"] },
    ToyKernel.inf "p" ["q", "c"], ToyKernel.inf "s" ["q"]] }]

def tier1Edit : Edit := .replaceMember 1 1 { name := "q", declared := some "C", path := ["p"] }

/-- **Tier 1, an edit inside a body whose type is declared**: the new node's typed form is the
only changed fact. The member's type and its owner's member set are in the footprint and rerun,
come out equal and are backdated, so `p`, `s`, the declaration's typed form and every other fact
are reused by trace without running. The store agrees with a fresh run, and `Same` holds outside
the footprint. -/
theorem tier1_body_edit :
    let r := (Rev.ofProgram tier1).validateAll .scalac
    let r' := r.edit .scalac tier1Edit
    r'.changed = [.typedMember 6] ∧
    r'.computed = [.namer (.decls (cls "C")), .namer (.mem (cls "C") "q"), .typedMember 6] ∧
    r'.reused.length = 11 ∧
    r'.agreesWithFresh .scalac = true ∧ sameOk .scalac r.tree tier1Edit = true := by
  decide

/-- `D.c` is a `String`, so retyping `q` as `D` changes what `q.c` is. -/
def tier2 : Program := tier1 ++ [{ name := "D", stats := [ToyKernel.m "c" "String"] }]

def tier2Edit : Edit := .replaceMember 1 1 { name := "q", declared := some "D", path := ["c"] }

/-- **Tier 2, an edit to a declared type**: `q`'s type changes, and with it exactly the facts whose
traces hold it: `p = q.c` and `s = q`, their typed forms, and `C`'s typed form. `c`'s type and
typed form, and `D`'s facts, are reused. -/
theorem tier2_signature_edit :
    let r := (Rev.ofProgram tier2).validateAll .scalac
    let r' := r.edit .scalac tier2Edit
    r'.changed = [.namer (.mem (cls "C") "q"), .namer (.mem (cls "C") "p"), .namer (.mem (cls "C") "s"),
      .typedDecl 1, .typedMember 8, .typedMember 4, .typedMember 5] ∧
    r'.computed = [.namer (.decls (cls "C")), .namer (.mem (cls "C") "q"), .namer (.mem (cls "C") "p"),
      .namer (.mem (cls "C") "s"), .typedDecl 1, .typedMember 8, .typedMember 4, .typedMember 5] ∧
    r'.agreesWithFresh .scalac = true ∧ sameOk .scalac r.tree tier2Edit = true := by
  decide

/-- `Use.r` reads a top-level `X` that does not exist; `s` and `t` do not. -/
def tier3a : Program := [int,
  { obj := true, name := "Use", stats := [ToyKernel.inf "r" ["X", "x"], ToyKernel.inf "s" ["t"], ToyKernel.m "t" "Int"] }]

def tier3aEdit : Edit := .insertDecl 1 { obj := true, name := "X", stats := [ToyKernel.m "x" "Int"] }

/-- **Tier 3a, a declaration added to the unit's scope**: the failed lookup of `X` in `r` is in
the footprint by name, reruns and now finds it; `s`, `t` and their typed forms are reused, and
`Use`'s nodes keep their ids although the insertion moved `Use` from index 1 to 2. -/
theorem tier3a_scope_insert :
    let r := (Rev.ofProgram tier3a).validateAll .scalac
    let r' := r.edit .scalac tier3aEdit
    r'.tree.nodeAt (.member 2 1) = some 3 ∧
    r'.changed = [.namer (.decls (obj "X")), .namer (.info (obj "X")), .namer (.mem (obj "X") "x"), .typedDecl 5,
      .typedMember 6, .namer (.mem (obj "Use") "r"), .typedDecl 1, .typedMember 2] ∧
    r'.reused = [.namer (.decls (cls "Int")), .namer (.info (cls "Int")), .typedDecl 0,
      .namer (.decls (obj "Use")), .namer (.info (obj "Use")), .namer (.mem (obj "Use") "s"), .namer (.mem (obj "Use") "t"),
      .typedMember 3, .typedMember 4] ∧
    r'.agreesWithFresh .scalac = true ∧ sameOk .scalac r.tree tier3aEdit = true := by
  decide

/-- `C extends P`: `j` finds `a` in `P`, `k` fails in both, `l` finds `j` in `C`. -/
def tier3b : Program := [int,
  { name := "P", stats := [ToyKernel.m "a" "Int"] },
  { name := "C", parent := some "P", stats := [ToyKernel.inf "j" ["a"], ToyKernel.inf "k" ["n"], ToyKernel.inf "l" ["j"]] }]

def tier3bEdit : Edit := .replaceDecl 1 { name := "P", stats := [ToyKernel.m "a" "Int", ToyKernel.m "n" "Int"] }

/-- **Tier 3b, a member added to a class scope**: `P`'s member set changes, and every lookup whose
trace holds it reruns, the one that found `a` there (`j`, backdated) and the one that failed there
(`k`, now typed); `l`, found in `C`'s own set, is reused. The failed lookup is in the trace because
[`lookupIn`](ToyNamer.lean) asks `decls` of each class it tries. -/
theorem tier3b_scope_member :
    let r := (Rev.ofProgram tier3b).validateAll .scalac
    let r' := r.edit .scalac tier3bEdit
    r'.changed = [.namer (.decls (cls "P")), .namer (.mem (cls "P") "n"), .typedDecl 7, .typedMember 8, .typedMember 9,
      .namer (.mem (cls "C") "k"), .typedDecl 3, .typedMember 5] ∧
    (r'.computed.contains (.namer (.mem (cls "C") "j")) ∧ ¬ r'.computed.contains (.namer (.mem (cls "C") "l"))) ∧
    r'.agreesWithFresh .scalac = true ∧ sameOk .scalac r.tree tier3bEdit = true := by
  decide

/-! ## Witness: I22, what a case class merges into its companion -/

/-- A case class `L` with a companion of its own, `object L { def k: Int }`. -/
def caseCompanion : Program := [int,
  { isCase := true, name := "L", params := [("a", "Int")] },
  { obj := true, name := "L", stats := [ToyKernel.m "k" "Int"] }]

/-- The companion replaced by a fresh parse with a second member. -/
def companionEdit : Edit := .replaceDecl 2 { obj := true, name := "L", stats := [ToyKernel.m "k" "Int", ToyKernel.m "k2" "Int"] }

/-- The case class replaced by a plain class. -/
def uncaseEdit : Edit := .replaceDecl 1 { name := "L", params := [("a", "Int")] }

/-- **I22 cannot happen here: the merge is a rule, not a mutation of the companion's tree.**
`apply` and `unapply` are in the companion's member set because `ToyNamer.synthetics` reads
whether the program has a case class of that name, not because the class's desugaring added
trees to the companion node. Replacing the companion by a fresh node keeps them; replacing the
case class by a plain class drops them from the companion it did not touch, because `decls` of the
companion is in the replaced class's footprint by name. Both revisions agree with a fresh run. -/
theorem replace_keeps_merged :
    let r := (Rev.ofProgram caseCompanion).validateAll .scalac
    let r1 := r.edit .scalac companionEdit
    let r2 := r.edit .scalac uncaseEdit
    (r.memo (.namer (.decls (obj "L")))).map (·.value) = some (.v (.names ["k", "apply", "unapply"])) ∧
    (r1.memo (.namer (.decls (obj "L")))).map (·.value) = some (.v (.names ["k", "k2", "apply", "unapply"])) ∧
    (r2.memo (.namer (.decls (obj "L")))).map (·.value) = some (.v (.names ["k"])) ∧
    r1.agreesWithFresh .scalac = true ∧ r2.agreesWithFresh .scalac = true ∧
    sameOk .scalac r.tree companionEdit = true ∧ sameOk .scalac r.tree uncaseEdit = true := by
  decide

/-! ## Witnesses: the editing session of `results-sessions.txt` on `big-file` -/

/-- `big-file.toy`: forty objects `On { def vn: Int; def wn = vn }`. -/
def bigFile : Program := int :: (List.range 40).map fun i =>
  { obj := true, name := s!"O{i+1}", stats := [ToyKernel.m s!"v{i+1}" "Int", ToyKernel.inf s!"w{i+1}" [s!"v{i+1}"]] }

/-- An edit at the end of the file: `O40.w40` gets a declared type, loses it, gets it back. -/
def bigEdit (k : Nat) : Edit :=
  .replaceMember 40 1 { name := "w40", declared := if k % 2 == 0 then some "Int" else none, path := ["v40"] }

inductive Step
  | req (p : Path)
  | edit (e : Edit)
  | whole

/-- A step's outcome: whether its answers are those of a fresh store of the revision, and the
facts whose rules it ran. -/
structure StepResult where
  fresh : Bool
  work : Nat
  deriving DecidableEq, Repr

def runSession (cut : Cut) : List Step → Rev → List StepResult → List StepResult
  | [], _, acc => acc.reverse
  | .req path :: rest, r, acc =>
    match request r.tree path with
    | none => runSession cut rest r (⟨false, 0⟩ :: acc)
    | some q =>
      let before := r.computed.length
      let (o, r') := r.ask cut q
      runSession cut rest r' (⟨o == (targeted cut r.tree q).1, r'.computed.length - before⟩ :: acc)
  | .edit e :: rest, r, acc =>
    let r' := r.edit cut e
    runSession cut rest r' (⟨r'.agreesWithFresh cut, r'.computed.length⟩ :: acc)
  | .whole :: rest, r, acc =>
    let before := r.computed.length
    let (os, r') := r.askAll cut (requests r.tree)
    runSession cut rest r' (⟨os == (requests r.tree).map fun q => (targeted cut r.tree q).1, r'.computed.length - before⟩ :: acc)

/-- The session of `run.sh --sessions`: a completion near the top, three edits at the end each
followed by it, a completion at the end, the whole unit. -/
def bigSession : List Step :=
  [.req (.member 1 1), .edit (bigEdit 0), .req (.member 1 1), .edit (bigEdit 1), .req (.member 1 1),
   .edit (bigEdit 2), .req (.member 1 1), .req (.member 40 1), .whole]

/-- **The session on `big-file`**: every answer is the fresh store's. The completion at the top
runs 4 rules. The first edit runs 279: `Rev.edit` re-validates every fact of the unit, and after
one targeted request 279 of the 283 have never been computed, so the first edit pays for the unit
(what dotc's whole-unit run pays on every edit). Each later edit runs the 3 rules of its footprint
(the member set and member type of `O40`, the new node's typed form; `O40`'s typed form is reused
since `w40`'s type is `Int` either way) and re-validates the other 280 by trace; the completions
and the whole unit after an edit run nothing. A fresh store runs 242 for each whole-unit request.
Re-validating on demand instead, so that the first edit costs 3 as well, needs entries that
remember the revision of their rule, not only of their value (future work). -/
theorem big_session :
    runSession .scalac bigSession (Rev.ofProgram bigFile) [] =
      [⟨true, 4⟩, ⟨true, 279⟩, ⟨true, 0⟩, ⟨true, 3⟩, ⟨true, 0⟩, ⟨true, 3⟩, ⟨true, 0⟩, ⟨true, 0⟩, ⟨true, 0⟩] ∧
    wholeWork .scalac (Tree.ofProgram bigFile) = 242 ∧ (facts (Tree.ofProgram bigFile)).length = 283 := by
  decide +kernel

/-! ## Future work: what the dotc spike found that the model has no concept of

I13 and I22 are absent by construction (`i13_burst_side_effect`, `replace_keeps_merged`): the
model has no fact produced as a side effect and no tree mutated by another's desugaring. The other
findings of the spike need concepts the model lacks.

* **I17, completers of skipped statements run in a later run.** The store here is per revision
  and a skipped node simply has no entry; nothing is entered into a scope with a completer that is
  run later. The smallest extension: a symbol-table layer between the namer and the store, where
  entering a declaration installs a completer (an entry with a rule but no value) whose owner run
  is recorded, and a rule that forces it in a later revision; the theorem to state is that the
  value is the later revision's rule, not the earlier's.
* **I20/I23, typed against skipped block statements.** The tree has no blocks: members are
  declarations of a template, each its own fact. The smallest extension: a member whose body is a
  list of statement nodes with local definitions visible to later ones, a typed form per statement,
  and the block's typed form as the list of them; targeting a statement then has to say which
  earlier statements it forces (their local symbols) and which it skips, and the bookkeeping of
  typed against skipped becomes part of the block's fact rather than of a mutable tree.
* **I24, the TyperState committed twice on a resume.** The model has no speculative state: a rule
  either finishes and its value is stored or does not. The smallest extension: a rule that writes
  into a nested, uncommitted layer of the store (constraints, or provisional facts) and a commit
  step, with resumption after an interrupt as re-running the rule from its last committed point;
  the theorem is that commit is idempotent on a resume (or the counterexample, as I24 is). -/

end ScalaTypes.ToyTree
