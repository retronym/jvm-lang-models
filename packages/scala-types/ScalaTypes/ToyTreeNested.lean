import ScalaTypes.ToyTree
/-!
# The toy's trees with one nested statement list: blocks, and bodies typed ahead

[`ToyTree`](ToyTree.lean) has two levels, declarations and their members, so a statement list is a
unit's declarations or a template's members, and no completer types a body under another request's
target. This file adds one level, a member whose body is a block, `def f = { def a = …; def b = …; b }`:
local member nodes (ids as for members) visible to later locals and to the result path, and paths
extended by a local index.

* **Targeting stays demand.** Typed forms are still facts keyed by node id: a local's signature
  (`localSig`) and typed form (`typedLocal`), and a block member's typed form, which lists its
  locals' typed forms. A block member without a result type has the signature of its result path,
  which asks the locals' signatures and nothing else: the completer of `f` forced from outside
  does not type `f`'s locals at all, and what it does not type it does not store. So a request at a
  path inside the block and one outside it answer as the whole check (`nested_targeted_eq_whole`).
* **The contrast, I21.** A kernel whose completer types the body *ahead* under the request's
  target, stubbing the locals off the path, and caches that typed body under the member's id
  (dotc's `TypedAhead`), so that a later request inside the block reads it. On a concrete example a
  request at `g = f` followed by one at `f`'s local `b` answers `b` as a stub, where the whole check
  types it; the rule the spike adopted, "a typed form cached under a node that does not contain the
  target is computed whole", restores agreement (`i21_typed_ahead_stubs`).

The one rule behind I21, I25 and I28: targeting is a property of the path from the root to the
target, and a tree typed off that path is typed whole, because its typed form outlives the request.
Over facts the rule holds by construction, since nothing is cached that is not a function of its
node; the kernel needs it stated.
-/

namespace ScalaTypes.ToyTreeNested

open Query Query.Lazy Query.Interrupt Query.Revision ScalaTypes.ToyNamer

/-! ## The tree with blocks -/

structure LocalNode where
  id : Nat
  m : Member
  deriving DecidableEq, Repr

/-- A block body: local members, each visible to the later ones and to the result, and the result
path. -/
structure Block where
  locals : List LocalNode
  result : List String
  deriving DecidableEq, Repr

/-- A member node; with a block, its `m.path` is empty and its body is the block. -/
structure NMember where
  id : Nat
  m : Member
  block : Option Block := none
  deriving DecidableEq, Repr

structure NDecl where
  id : Nat
  head : Decl
  members : List NMember
  deriving DecidableEq, Repr

structure NTree where
  decls : List NDecl
  deriving DecidableEq, Repr

def NDecl.toDecl (d : NDecl) : Decl := { d.head with stats := d.members.map (.member ·.m) }
def NDecl.ref (d : NDecl) : Ref := if d.head.obj then obj d.head.name else cls d.head.name
def NTree.program (t : NTree) : Program := t.decls.map NDecl.toDecl

/-- A position: a declaration, a member, or a local of a member's block, by index. -/
inductive NPath
  | decl (i : Nat)
  | member (i j : Nat)
  | inBlock (i j k : Nat)
  deriving DecidableEq, Repr

def NTree.blockAt (t : NTree) (i j : Nat) : Option (NMember × Block) :=
  (t.decls[i]?).bind fun d => (d.members[j]?).bind fun m => m.block.map (m, ·)

def NTree.nodeAt (t : NTree) : NPath → Option Nat
  | .decl i => (t.decls[i]?).map (·.id)
  | .member i j => (t.decls[i]?).bind fun d => (d.members[j]?).map (·.id)
  | .inBlock i j k => (t.blockAt i j).bind fun (_, b) => (b.locals[k]?).map (·.id)

def NTree.paths (t : NTree) : List NPath :=
  t.decls.zipIdx.flatMap fun (d, i) => NPath.decl i :: d.members.zipIdx.flatMap fun (m, j) =>
    NPath.member i j :: ((m.block.map (·.locals)).getD []).zipIdx.map fun (_, k) => NPath.inBlock i j k

def findDecl' (t : NTree) (id : Nat) : Option NDecl := t.decls.find? (·.id == id)

def findMember' (t : NTree) (id : Nat) : Option (NDecl × NMember) :=
  t.decls.findSome? fun d => (d.members.find? (·.id == id)).map (d, ·)

/-- A local by id: its declaration, its member, the block, and its index there. -/
def findLocal (t : NTree) (id : Nat) : Option (NDecl × NMember × Block × Nat) :=
  t.decls.findSome? fun d => d.members.findSome? fun m => m.block.bind fun b =>
    (b.locals.zipIdx.find? (·.1.id == id)).map fun (_, k) => (d, m, b, k)

/-- The block member `n` of `r` without a result type, whose signature is its block's result. -/
def blockMemberOf (t : NTree) (r : Ref) (n : String) : Option (NDecl × NMember × Block) :=
  t.decls.findSome? fun d =>
    if d.ref == r then d.members.findSome? fun m =>
      if m.m.name == n && m.m.declared.isNone then m.block.map (d, m, ·) else none
    else none

/-! ## Typed forms as facts -/

inductive NFact
  | namer (f : Fact)
  | typedDecl (id : Nat)
  | typedMember (id : Nat)
  /-- A local's type, as the namer's `mem` is a member's. -/
  | localSig (id : Nat)
  /-- A local's typed form: its type, and its body typed against a declared type. -/
  | typedLocal (id : Nat)
  deriving DecidableEq, Repr

/-- A local in a block's typed form: name, type, typed body. -/
abbrev LocalForm := String × Value × Option Value

inductive NValue
  | v (x : Value)
  | member (sig : Value) (body : Option Value)
  /-- A block member's typed form: its type and its locals' typed forms. -/
  | block (sig : Value) (locals : List LocalForm)
  | bodies (bs : List (String × List (String × Value)))
  deriving DecidableEq, Repr

def NValue.toValue : NValue → Value
  | .v x => x
  | _ => .err "not a value"

abbrev NRule (α : Type) := Task NFact (fun _ => NValue) α

def liftN (t : Rule Value) : NRule Value :=
  t.rename (fun pr => NFact.namer (fact pr)) (fun _ tv => tv.toValue)

def askV (q : NFact) : NRule Value := .ask q fun nv => .pure nv.toValue

/-- The type of a path inside a block, with `visible` the locals before it: a first name that is
one of them is typed by the local's signature, otherwise the path is typed from the owner as a
member's is. -/
def blockPath (cut : Cut) (p : Program) (r : Ref) (visible : List LocalNode) : List String → NRule Value
  | [] => pure (.err "empty path")
  | first :: rest =>
    match visible.find? (·.m.name == first) with
    | some l => do
      let v ← askV (.localSig l.id)
      match v with
      | .typed ty => liftN (walk cut p ty rest)
      | other => pure other
    | none => liftN (typePath cut p r (first :: rest))

def memberTypesN (r : Ref) : List String → NRule (List (String × Value))
  | [] => pure []
  | n :: ns => do
    let v ← askV (.namer (.mem r n))
    let rest ← memberTypesN r ns
    pure ((n, v) :: rest)

def bodyOfN (r : Ref) : NRule (List (String × Value)) := do
  let v ← askV (.namer (.decls r))
  match v with
  | .names ns => memberTypesN r (ToyKernel.sortedSet ns)
  | other => pure [("<decls>", other)]

def localForms : List LocalNode → NRule (List LocalForm)
  | [] => pure []
  | l :: ls => do
    let f ← (Task.ask (NFact.typedLocal l.id) pure : NRule NValue)
    let rest ← localForms ls
    pure ((match f with
      | .member s b => (l.m.name, s, b)
      | _ => (l.m.name, .err "not a local", none)) :: rest)

/-- The rules: `ToyTree.rulesOf`'s, with the namer's `mem` of a block member without a result type
being its result path's type in the block (the completer, which asks the locals' signatures only),
and the local facts typed in the block's scope. -/
def rulesOf (cut : Cut) (t : NTree) : Rules NFact NValue
  | .namer f =>
    let namer := (liftN (ToyNamer.rulesOf cut t.program f)).bind fun v => pure (.v v)
    match f with
    | .mem r n =>
      match blockMemberOf t r n with
      | some (d, _, b) => (blockPath cut t.program d.ref b.locals b.result).bind fun v => pure (.v v)
      | none => namer
    | _ => namer
  | .typedMember id =>
    match findMember' t id with
    | none => pure (.v (.err "no such node"))
    | some (d, m) => do
      let sig ← askV (.namer (.mem d.ref m.m.name))
      match m.block with
      | some b => do let ls ← localForms b.locals; pure (.block sig ls)
      | none =>
        if m.m.declared.isSome && !m.m.path.isEmpty then
          let body ← liftN (typePath cut t.program d.ref m.m.path)
          pure (.member sig (some body))
        else pure (.member sig none)
  | .localSig id =>
    match findLocal t id with
    | none => pure (.v (.err "no such node"))
    | some (d, _, b, k) =>
      match b.locals[k]? with
      | none => pure (.v (.err "no such node"))
      | some l =>
        match l.m.declared with
        | some ty => pure (.v (declaredType t.program ty))
        | none => (blockPath cut t.program d.ref (b.locals.take k) l.m.path).bind fun v => pure (.v v)
  | .typedLocal id =>
    match findLocal t id with
    | none => pure (.v (.err "no such node"))
    | some (d, _, b, k) =>
      match b.locals[k]? with
      | none => pure (.v (.err "no such node"))
      | some l => do
        let sig ← askV (.localSig id)
        if l.m.declared.isSome && !l.m.path.isEmpty then
          let body ← blockPath cut t.program d.ref (b.locals.take k) l.m.path
          pure (.member sig (some body))
        else pure (.member sig none)
  | .typedDecl id =>
    match findDecl' t id with
    | none => pure (.v (.err "no such node"))
    | some d => do
      let b ← bodyOfN d.ref
      pure (.bodies [(ToyKernel.bodyKey d.toDecl, b)])

/-- The facts of a tree: the namer's for each declaration, and the typed forms of each node. -/
def facts (t : NTree) : List NFact :=
  let p := t.program
  t.decls.flatMap fun d =>
    [.namer (.decls d.ref), .namer (.info d.ref)] ++ (ownNames p d.ref).map (NFact.namer <| .mem d.ref ·) ++
    [.typedDecl d.id] ++ d.members.flatMap fun m =>
      .typedMember m.id :: ((m.block.map (·.locals)).getD []).flatMap fun l => [.localSig l.id, .typedLocal l.id]

def request (t : NTree) : NPath → Option NFact
  | .decl i => (t.nodeAt (.decl i)).map .typedDecl
  | p@(.member ..) => (t.nodeAt p).map .typedMember
  | p@(.inBlock ..) => (t.nodeAt p).map .typedLocal

def requests (t : NTree) : List NFact := t.paths.filterMap (request t)

/-! ## Targeting -/

def targeted (cut : Cut) (t : NTree) (q : NFact) : Out NFact NValue × Memo NFact NValue :=
  reval (rulesOf cut t) (fun _ => false) empty 0 ToyTree.fuel [] empty q

def whole (cut : Cut) (t : NTree) : Memo NFact NValue :=
  (fresh (rulesOf cut t) 0 ToyTree.fuel (requests t)).2

def afterWhole (cut : Cut) (t : NTree) (q : NFact) : Out NFact NValue :=
  (reval (rulesOf cut t) (fun _ => false) empty 0 ToyTree.fuel [] (whole cut t) q).1

def targetedEqWhole (cut : Cut) (t : NTree) : Bool :=
  (requests t).all fun q => (targeted cut t q).1 == afterWhole cut t q

def targetedWithinWhole (cut : Cut) (t : NTree) : Bool :=
  (requests t).all fun q =>
    (facts t).all fun f => match (targeted cut t q).2 f, whole cut t f with
      | some e, some e' => e.value == e'.value
      | some _, none => false
      | none, _ => true

/-- The answer at a path, targeted from an empty store. -/
def answerAt (cut : Cut) (t : NTree) (p : NPath) : Option (Out NFact NValue) :=
  (request t p).map fun q => (targeted cut t q).1

/-! ## Witness: a block, targeted inside and outside it -/

/-- ```scala
class C {
  def c: Int
  def f = { def a = c; def b: Int = a; b }
  def g = f
}
```
Ids: `Int` 0, `C` 1, `c` 2, `f` 3, `a` 4, `b` 5, `g` 6. -/
def blockToy : NTree := ⟨[
  ⟨0, int, []⟩,
  ⟨1, { name := "C" }, [
    ⟨2, { name := "c", declared := some "Int" }, none⟩,
    ⟨3, { name := "f" }, some ⟨[⟨4, { name := "a", path := ["c"] }⟩, ⟨5, { name := "b", declared := some "Int", path := ["a"] }⟩], ["b"]⟩⟩,
    ⟨6, { name := "g", path := ["f"] }, none⟩]⟩]⟩

def intTy : Value := ty (.ref (cls "Int"))

/-- **Targeting is demand, with a block.** At every path of `blockToy`, under the fine and the
scalac cut, a targeted request answers as the whole check and stores only what the whole check
stores. At `b`, inside the block, the answer is its typed form (`Int`, body `a : Int`); at `g = f`,
outside it, `g`'s type is `Int` through `f`'s completer, which asked the signatures of `b` and `a`
and stored no local's typed form: what the request did not type, it did not cache. -/
theorem nested_targeted_eq_whole :
    (∀ cut ∈ [Cut.fine, .scalac], targetedEqWhole cut blockToy = true ∧ targetedWithinWhole cut blockToy = true) ∧
    answerAt .scalac blockToy (.inBlock 1 1 1) = some (.ok (.member intTy (some intTy))) ∧
    answerAt .scalac blockToy (.member 1 2) = some (.ok (.member intTy none)) ∧
    (targeted .scalac blockToy (.typedMember 6)).2 (.localSig 5) ≠ none ∧
    (targeted .scalac blockToy (.typedMember 6)).2 (.typedLocal 4) = none ∧
    (targeted .scalac blockToy (.typedMember 6)).2 (.typedLocal 5) = none := by
  decide

/-! ## Witness: I21, a body typed ahead with stubs and cached -/

/-- The whole check's value of a fact. -/
def wholeValue (cut : Cut) (t : NTree) (q : NFact) : Option NValue := (whole cut t q).map (·.value)

def stub (n : String) : LocalForm := (n, .err "<stub>", none)

/-- The typed form of the block of member `m`, keeping the locals at the indices `keep` says (the
whole check's typed forms) and stubbing the rest; the signature is the whole check's, since the
result's type asks the locals' signatures, which a stub does not touch. -/
def blockUnder (cut : Cut) (t : NTree) (m : NMember) (b : Block) (keep : Nat → Bool) : NValue :=
  let sig := ((wholeValue cut t (.typedMember m.id)).bind fun | .block s _ => some s | _ => none).getD (.err "?")
  .block sig (b.locals.zipIdx.map fun (l, k) =>
    if keep k then
      match wholeValue cut t (.typedLocal l.id) with
      | some (.member s bd) => (l.m.name, s, bd)
      | _ => stub l.m.name
    else stub l.m.name)

/-- Is local `k` of the block at `(i, j)` on the path to `target`? -/
def onPath (target : NPath) (i j k : Nat) : Bool :=
  match target with
  | .decl i' => i' == i
  | .member i' j' => i' == i && j' == j
  | .inBlock i' j' k' => i' == i && j' == j && k' == k

/-- Does `target` lie inside the block at `(i, j)`? -/
def inside (target : NPath) (i j : Nat) : Bool :=
  match target with
  | .decl i' => i' == i
  | .member i' j' | .inBlock i' j' _ => i' == i && j' == j

/-- How a completer types a body ahead: under the request's target (the spike before I21's fix),
or whole when the target is not inside it (the fix). -/
inductive Policy | underTarget | wholeOffPath
  deriving DecidableEq, Repr

/-- The bodies typed ahead: member id and its cached typed form (dotc's `TypedAhead`). -/
abbrev Ahead := List (Nat × NValue)

/-- The block members whose completers a request runs: those without a result type whose
signature the request forces. -/
def forcedBlocks (cut : Cut) (t : NTree) (q : NFact) : List (Nat × Nat × NMember × Block) :=
  t.decls.zipIdx.flatMap fun (d, i) => d.members.zipIdx.filterMap fun (m, j) =>
    match m.block with
    | some b =>
      if m.m.declared.isNone && ((targeted cut t q).2 (.namer (.mem d.ref m.m.name))).isSome
      then some (i, j, m, b) else none
    | none => none

/-- A request in the kernel: each completer the request runs types its body ahead, unless already
cached, and caches it; a request inside a block reads the block's cached typed form if there is
one, and otherwise types the block under its own target; a block member's typed form is the cached
one if there is one. Everything else is the facts' answer. -/
def kernelAsk (pol : Policy) (cut : Cut) (t : NTree) (ahead : Ahead) (path : NPath) : Option NValue × Ahead :=
  match request t path with
  | none => (none, ahead)
  | some q =>
    let ahead := (forcedBlocks cut t q).foldl (fun acc (i, j, m, b) =>
      if (acc.lookup m.id).isSome then acc
      else
        let keep : Nat → Bool := match pol with
          | .underTarget => fun k => onPath path i j k
          | .wholeOffPath => fun k => !inside path i j || onPath path i j k
        (m.id, blockUnder cut t m b keep) :: acc) ahead
    let ans := match path with
      | .inBlock i j k =>
        (t.blockAt i j).bind fun (m, b) =>
          let form := (ahead.lookup m.id).getD (blockUnder cut t m b (onPath path i j))
          match form with
          | .block _ ls => (ls[k]?).map fun (_, s, bd) => NValue.member s bd
          | _ => none
      | .member i j =>
        match t.blockAt i j with
        | some (m, _) => (ahead.lookup m.id) <|> wholeValue cut t q
        | none => wholeValue cut t q
      | .decl _ => wholeValue cut t q
    (ans, ahead)

/-- A run of the kernel: requests in order, sharing the bodies typed ahead. -/
def kernelSession (pol : Policy) (cut : Cut) (t : NTree) : List NPath → Ahead → List (Option NValue)
  | [], _ => []
  | p :: ps, ahead => let (a, ahead') := kernelAsk pol cut t ahead p; a :: kernelSession pol cut t ps ahead'

/-- The whole check's answers. -/
def wholeAnswers (cut : Cut) (t : NTree) (ps : List NPath) : List (Option NValue) :=
  ps.map fun p => (request t p).bind (wholeValue cut t)

/-- **I21 on `blockToy`**: a request at `g = f`, then one at `f`'s local `b`, in one run. `g`'s
typing forces `f`'s signature, whose completer types `f`'s body ahead; under `g`'s target no local
of `f` is on the path, so both are stubbed, and the cached body answers the request at `b` with a
stub where the whole check (and demand, `nested_targeted_eq_whole`) types it. In the other order
nothing is typed ahead before `b` is asked, and the answers agree: the bug needs the completer to
run first. With the fix, a body typed ahead under a target outside it is typed whole, and every
two-request run on every pair of paths answers as the whole check. -/
theorem i21_typed_ahead_stubs :
    kernelSession .underTarget .scalac blockToy [.member 1 2, .inBlock 1 1 1] [] =
      [some (.member intTy none), some (.member (.err "<stub>") none)] ∧
    wholeAnswers .scalac blockToy [.member 1 2, .inBlock 1 1 1] =
      [some (.member intTy none), some (.member intTy (some intTy))] ∧
    kernelSession .underTarget .scalac blockToy [.inBlock 1 1 1, .member 1 2] [] =
      wholeAnswers .scalac blockToy [.inBlock 1 1 1, .member 1 2] ∧
    (∀ p ∈ blockToy.paths, ∀ p' ∈ blockToy.paths,
      kernelSession .wholeOffPath .scalac blockToy [p, p'] [] = wholeAnswers .scalac blockToy [p, p']) := by
  decide +kernel

end ScalaTypes.ToyTreeNested
