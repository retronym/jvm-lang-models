import ScalaTypes.ToyTree
import ScalaTypes.ToySpace
/-!
# The body-edit rule: an edit inside a body whose type is declared keeps the run

retronym/scala3#84 built, behind `-Yinteractive-body-edits`, the rule IntelliJ's
`BlockModificationTracker` and K2's in-block modification follow: when the edit lies inside the
right-hand side of one member definition with a declared result type, the run is kept, every other
statement's typed tree and every symbol survive, and the edited member is re-indexed with its old
symbols and made a skipped statement (interactive-session.md §12, `BodyEdit.scala`). The tree model
([`ToyTree`](ToyTree.lean)) stated the rule on one example, [`tier1_body_edit`](ToyTree.lean). This
file states it for every program of the toy language and every single-member body edit, and
catalogues the features under which it is unsound.

* **Erasure.** The rule's semantic content is that no fact outside the member's own typed form
  reads a declared member's body. `erase` deletes the path of every member with a declared type;
  [`rulesOf_erase`](#) proves that the namer's rules of every fact of every program are the rules of
  the erased program, so two programs that differ only in such a body have the same symbol table.
  A general proof, by induction on the namer's functions, not `decide`.
* **The tree.** [`bodyEdit_rules_eq`](#) lifts this to the tree's facts: after a body edit of the
  node `old` to the new node `t.next`, every typed form of another node and every namer fact has
  the same rule as before (the same `Task`, so the same value and trace under every oracle). That
  is exactly the `Same` hypothesis of [`Query.Revision.reuse_sound`](../../query/Query/Revision.lean)
  with `same` = "not the edited node", so keeping the store across the edit is sound for every
  program (`bodyEdit_kept_run_sound`), with the edited member's typed form the only fact that must
  be recomputed, and only when a request asks for it (the skipped statement).
* **Witnesses by `decide`** on a space of programs and edits: the kept run runs no rule, the
  skipped node's later request answers as a fresh store, the diagnostics (the error values of
  facts, keyed by the fact that produced them, §12 "Diagnostics", I69) outside the member are
  unchanged.
* **The catalogue.** What makes the rule unsound, each a theorem on an example: an inferred result
  type (the member's own type fact changes and the facts downstream with it); an `inline` member,
  modelled as a caller whose typed form splices the inlinee's body (I28), where a sibling's typed
  form changes under a body edit although no namer fact does; an `export` in a template body is a
  member set, not a body. What the toy cannot show (a sealed parent's `children`, local givens,
  default getters, annotations, provenance) is argued from dotc in the note.
-/

namespace ScalaTypes.ToyBodyEdit

open Query Query.Lazy Query.Revision ScalaTypes.ToyNamer ScalaTypes.ToyTree

/-! ## Erasure: the program without the bodies of its declared members -/

/-- A member with its body erased when its type is declared: what the signature alone says. -/
def eraseMember (m : Member) : Member :=
  { m with path := if m.declared.isSome then [] else m.path }

def eraseStat : Stat → Stat
  | .member m => .member (eraseMember m)
  | s => s

def eraseDecl (d : Decl) : Decl := { d with stats := d.stats.map eraseStat }

/-- The program with every declared member's body erased. -/
def erase (p : Program) : Program := p.map eraseDecl

@[simp] theorem eraseMember_name (m : Member) : (eraseMember m).name = m.name := rfl
@[simp] theorem eraseMember_declared (m : Member) : (eraseMember m).declared = m.declared := rfl
@[simp] theorem eraseMember_deprecated (m : Member) : (eraseMember m).deprecated = m.deprecated := rfl
@[simp] theorem eraseDecl_name (d : Decl) : (eraseDecl d).name = d.name := rfl
@[simp] theorem eraseDecl_obj (d : Decl) : (eraseDecl d).obj = d.obj := rfl
@[simp] theorem eraseDecl_isCase (d : Decl) : (eraseDecl d).isCase = d.isCase := rfl
@[simp] theorem eraseDecl_isImplicit (d : Decl) : (eraseDecl d).isImplicit = d.isImplicit := rfl
@[simp] theorem eraseDecl_params (d : Decl) : (eraseDecl d).params = d.params := rfl
@[simp] theorem eraseDecl_parent (d : Decl) : (eraseDecl d).parent = d.parent := rfl
@[simp] theorem erase_length (p : Program) : (erase p).length = p.length := List.length_map _

theorem eraseDecl_members (d : Decl) : (eraseDecl d).members = d.members.map eraseMember := by
  unfold Decl.members eraseDecl
  simp only [List.filterMap_map, List.map_filterMap]
  congr 1; funext s; cases s <;> rfl

theorem eraseDecl_exports (d : Decl) : (eraseDecl d).exports = d.exports := by
  unfold Decl.exports eraseDecl
  simp only [List.filterMap_map]
  congr 1; funext s; cases s <;> rfl

theorem findDecl_erase (p : Program) (r : Ref) : findDecl (erase p) r = (findDecl p r).map eraseDecl := by
  unfold findDecl erase
  rw [List.find?_map, List.any_map]
  simp only [Function.comp_def, eraseDecl_name, eraseDecl_obj, eraseDecl_isCase]
  cases p.find? fun d => d.name == r.name && d.obj == r.obj with
  | some d => rfl
  | none =>
    by_cases h : (r.obj && p.any fun d => d.name == r.name && !d.obj && d.isCase) = true <;>
      simp only [h, ↓reduceIte, Option.map_some, Option.map_none, Bool.false_eq_true] <;> rfl

theorem isCaseClass_erase (p : Program) (n : String) : isCaseClass (erase p) n = isCaseClass p n := by
  unfold isCaseClass erase
  rw [List.any_map]; rfl

theorem synthetics_erase (p : Program) (r : Ref) : synthetics (erase p) r = synthetics p r := by
  simp only [synthetics, isCaseClass_erase]

theorem ownNames_erase (p : Program) (r : Ref) : ownNames (erase p) r = ownNames p r := by
  unfold ownNames
  rw [findDecl_erase, synthetics_erase]
  cases findDecl p r with
  | none => rfl
  | some d =>
    simp only [Option.map_some, eraseDecl_isCase, eraseDecl_obj, eraseDecl_params, eraseDecl_members,
      List.map_map]
    rfl

theorem isDeprecated_erase (p : Program) (o : Ref) (n : String) :
    isDeprecated (erase p) o n = isDeprecated p o n := by
  unfold isDeprecated
  rw [findDecl_erase]
  cases findDecl p o with
  | none => rfl
  | some d =>
    simp only [Option.map_some, Option.bind_some, eraseDecl_members, List.find?_map, Function.comp_def,
      eraseMember_name, Option.map_map, eraseMember_deprecated]

theorem declaredType_erase (p : Program) (t : String) : declaredType (erase p) t = declaredType p t := by
  simp only [declaredType, findDecl_erase, Option.isSome_map]

theorem exportSource_erase (p : Program) (src : String) : exportSource (erase p) src = exportSource p src := by
  simp only [exportSource, findDecl_erase, Option.isSome_map]

theorem visibleNames_erase (cut : Cut) (p : Program) (r : Ref) :
    visibleNames cut (erase p) r = visibleNames cut p r := by
  simp only [visibleNames, ownNames_erase]

theorem lookupIn_erase (cut : Cut) (p : Program) :
    ∀ (fuel : Nat) (r : Ref) (n : String), lookupIn cut (erase p) fuel r n = lookupIn cut p fuel r n := by
  intro fuel
  induction fuel with
  | zero => intro r n; rfl
  | succ fuel ih => intro r n; simp only [lookupIn, visibleNames_erase, ih]

theorem findImplicit_erase (cut : Cut) (p : Program) (r : Ref) (n : String) :
    ∀ ds : List Decl, findImplicit cut (erase p) r n (ds.map eraseDecl) = findImplicit cut p r n ds := by
  intro ds
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, findImplicit, eraseDecl_isImplicit, eraseDecl_obj, eraseDecl_params,
      eraseDecl_name, erase_length, lookupIn_erase, ih]

theorem findImplicit_erase' (cut : Cut) (p : Program) (r : Ref) (n : String) :
    findImplicit cut (erase p) r n (erase p) = findImplicit cut p r n p :=
  findImplicit_erase cut p r n p

theorem step_erase (acc : Typed) (p : Program) (o : Ref) (n : String) (via : Option Via) (v : Value) :
    step acc (erase p) o n via v = step acc p o n via v := by
  simp only [step, isDeprecated_erase]

theorem walk_erase (cut : Cut) (p : Program) :
    ∀ (path : List String) (acc : Typed), walk cut (erase p) acc path = walk cut p acc path := by
  intro path
  induction path with
  | nil => intro acc; rfl
  | cons n rest ih =>
    intro acc
    simp only [walk, lookupIn_erase, erase_length, findImplicit_erase', step_erase, ih]

theorem typePath_erase (cut : Cut) (p : Program) (r : Ref) (path : List String) :
    typePath cut (erase p) r path = typePath cut p r path := by
  cases path with
  | nil => rfl
  | cons first rest =>
    simp only [typePath, lookupIn_erase, erase_length, step_erase, walk_erase, findDecl_erase,
      Option.isSome_map]

theorem exportedNames_erase (cut : Cut) (p : Program) (src : String) (names : Option (List String)) :
    exportedNames cut (erase p) src names = exportedNames cut p src names := by
  simp only [exportedNames, exportSource_erase, visibleNames_erase]

theorem declsRule_erase (cut : Cut) (p : Program) :
    ∀ (es : List (String × Option (List String))) (acc : List String),
      declsRule cut (erase p) es acc = declsRule cut p es acc := by
  intro es
  induction es with
  | nil => intro acc; rfl
  | cons e es ih =>
    intro acc
    obtain ⟨src, names⟩ := e
    simp only [declsRule, exportedNames_erase, ih]

theorem forwardedType_erase (cut : Cut) (p : Program) (n : String) :
    ∀ es : List (String × Option (List String)), forwardedType cut (erase p) n es = forwardedType cut p n es := by
  intro es
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨src, names⟩ := e
    simp only [forwardedType, exportedNames_erase, exportSource_erase, ih]

/-- **No fact of the namer reads a declared member's body.** The rule of every fact of every
program, under every cut, is the rule of the program with those bodies erased: a member's type
when declared is `declaredType`; the member sets, parents, exports and the paths of the inferred
members read names, headers, declared types and the deprecation flag, never a declared member's
path. So two programs that differ only in the body of a member with a declared type have the same
rules for every fact: the same symbol table. -/
theorem rulesOf_erase (cut : Cut) (p : Program) (f : Fact) :
    ToyNamer.rulesOf cut (erase p) f = ToyNamer.rulesOf cut p f := by
  cases f with
  | info r =>
    simp only [ToyNamer.rulesOf, findDecl_erase]
    cases findDecl p r <;> rfl
  | decls r =>
    simp only [ToyNamer.rulesOf, findDecl_erase, ownNames_erase]
    cases findDecl p r with
    | none => rfl
    | some d => simp only [Option.map_some, eraseDecl_exports, declsRule_erase]
  | mem r n =>
    simp only [ToyNamer.rulesOf, findDecl_erase, synthetics_erase]
    cases findDecl p r with
    | none => rfl
    | some d =>
      simp only [Option.map_some, eraseDecl_params, eraseDecl_members, eraseDecl_exports, List.find?_map,
        Function.comp_def, eraseMember_name, declaredType_erase, forwardedType_erase]
      split
      · rfl
      · cases d.params.find? (·.1 == n) with
        | some pr => rfl
        | none =>
          cases d.members.find? (·.name == n) with
          | none => simp only [Option.map_none]
          | some m =>
            simp only [Option.map_some, eraseMember_declared]
            cases hd : m.declared with
            | some t => rfl
            | none =>
              simp only [eraseMember, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, typePath_erase]

/-! ## The tree: a body edit leaves every other fact's rule as it was -/

/-- A body edit of the member at `(i, j)`: a replacement of that member by one with the same name,
declared type and deprecation (the signature, as `BodyEdit.classify` compares it modulo the
region), the type declared (`ineligible` refuses an inferred one), and a body on both sides (an
abstract member gaining a body changes `Deferred`, which in dotc is a changed signature tree). -/
def isBodyEdit (t : Tree) : Edit → Bool
  | .replaceMember i j m' =>
    match t.decls[i]? with
    | some d =>
      match d.members[j]? with
      | some old =>
        old.m.name == m'.name && old.m.declared.isSome && old.m.declared == m'.declared &&
          old.m.deprecated == m'.deprecated && !old.m.path.isEmpty && !m'.path.isEmpty
      | none => false
    | none => false
  | _ => false

theorem map_setAt {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat) (x : α), (∀ y, l[i]? = some y → f x = f y) → (setAt l i x).map f = l.map f
  | [], _, _, _ => rfl
  | y :: _, 0, x, h => by simp only [setAt, List.map_cons, h y rfl]
  | y :: ys, n + 1, x, h => by
    simp only [setAt, List.map_cons]
    rw [map_setAt f ys n x (fun z hz => h z (by simpa using hz))]

theorem any_setAt {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : Nat) (x : α), (∀ y, l[i]? = some y → p x = p y) → (setAt l i x).any p = l.any p
  | [], _, _, _ => rfl
  | y :: _, 0, x, h => by simp only [setAt, List.any_cons, h y rfl]
  | y :: ys, n + 1, x, h => by
    simp only [setAt, List.any_cons]
    rw [any_setAt p ys n x (fun z hz => h z (by simpa using hz))]

theorem find?_setAt_of_false {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : Nat) (x : α), p x = false → (∀ y, l[i]? = some y → p y = false) →
      (setAt l i x).find? p = l.find? p
  | [], _, _, _, _ => rfl
  | y :: _, 0, x, hx, h => by simp only [setAt, List.find?_cons, hx, h y rfl]
  | y :: ys, n + 1, x, hx, h => by
    simp only [setAt, List.find?_cons]
    rw [find?_setAt_of_false p ys n x hx (fun z hz => h z (by simpa using hz))]

theorem find?_setAt_map {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ (l : List α) (i : Nat) (x : α), (∀ y, l[i]? = some y → p x = p y ∧ f x = f y) →
      ((setAt l i x).find? p).map f = (l.find? p).map f
  | [], _, _, _ => rfl
  | y :: _, 0, x, h => by
    obtain ⟨hp, hf⟩ := h y rfl
    simp only [setAt, List.find?_cons, hp]
    cases p y <;> simp [hf]
  | y :: ys, n + 1, x, h => by
    simp only [setAt, List.find?_cons]
    cases p y with
    | true => rfl
    | false => exact find?_setAt_map p f ys n x (fun z hz => h z (by simpa using hz))

theorem findSome?_setAt {α β : Type} (g : α → Option β) :
    ∀ (l : List α) (i : Nat) (x : α), (∀ y, l[i]? = some y → g x = g y) → (setAt l i x).findSome? g = l.findSome? g
  | [], _, _, _ => rfl
  | y :: _, 0, x, h => by simp only [setAt, List.findSome?_cons, h y rfl]
  | y :: ys, n + 1, x, h => by
    simp only [setAt, List.findSome?_cons]
    rw [findSome?_setAt g ys n x (fun z hz => h z (by simpa using hz))]

/-- The typed-member rule as a function of what the node says (its owner's reference and its
member) and the program. -/
def typedMemberOf (cut : Cut) (p : Program) : Option (Ref × Member) → TRule TValue
  | none => pure (.v (.err "no such node"))
  | some (r, m) => do
    let sig ← askNamer (.mem r m.name)
    if m.declared.isSome && !m.path.isEmpty then
      let body ← lift (typePath cut p r m.path)
      pure (.member sig (some body))
    else pure (.member sig none)

def memberProj (dm : DeclNode × MemberNode) : Ref × Member := (dm.1.ref, dm.2.m)

theorem rulesOf_typedMember (cut : Cut) (t : Tree) (id : Nat) :
    ToyTree.rulesOf cut t (.typedMember id) = typedMemberOf cut t.program ((findMemberNode t id).map memberProj) := by
  unfold ToyTree.rulesOf
  cases h : findMemberNode t id with
  | none => simp only [h]; rfl
  | some dm => obtain ⟨d, m⟩ := dm; simp only [h]; rfl

theorem typedMemberOf_erase (cut : Cut) (p : Program) (o : Option (Ref × Member)) :
    typedMemberOf cut (erase p) o = typedMemberOf cut p o := by
  cases o with
  | none => rfl
  | some rm => obtain ⟨r, m⟩ := rm; simp only [typedMemberOf, typePath_erase]

/-- The typed-declaration rule as a function of the headers of the unit and of the node's. -/
def typedDeclOf : List Decl → Option Decl → TRule TValue
  | _, none => pure (.v (.err "no such node"))
  | heads, some h => do
    let r := if h.obj then obj h.name else cls h.name
    let b ← bodyOf r
    let hasCompanion := heads.any fun o => o.obj && o.name == h.name
    if h.isCase && !h.obj && !hasCompanion then
      let cb ← bodyOf (obj h.name)
      pure (.bodies [(ToyKernel.bodyKey h, b), (s!"object {h.name} (synthetic)", cb)])
    else pure (.bodies [(ToyKernel.bodyKey h, b)])

theorem rulesOf_typedDecl (cut : Cut) (t : Tree) (id : Nat) :
    ToyTree.rulesOf cut t (.typedDecl id) = typedDeclOf (t.decls.map (·.head)) ((findDeclNode t id).map (·.head)) := by
  unfold ToyTree.rulesOf
  cases h : findDeclNode t id with
  | none => simp only [h]; rfl
  | some d =>
    simp only [h, Option.map_some, typedDeclOf, List.any_map]
    rfl

theorem rulesOf_namer (cut : Cut) (t : Tree) (f : Fact) :
    ToyTree.rulesOf cut t (.namer f) = (lift (ToyNamer.rulesOf cut (erase t.program) f)).bind fun v => pure (.v v) := by
  simp only [ToyTree.rulesOf, rulesOf_erase]

/-- The node the edit replaces and the node it makes. -/
structure Edited where
  i : Nat
  j : Nat
  d : DeclNode
  old : MemberNode
  m' : Member

/-- The tree after the body edit, spelt out. -/
theorem apply_replaceMember (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d) :
    t.apply (.replaceMember e.i e.j e.m') =
      ⟨setAt t.decls e.i { e.d with members := setAt e.d.members e.j ⟨t.next, e.m'⟩ }, t.next + 1⟩ := by
  simp only [Tree.apply, hd]

theorem eraseDecl_toDecl (d : DeclNode) :
    eraseDecl d.toDecl = { d.head with stats := d.members.map fun mn => .member (eraseMember mn.m) } := by
  simp only [eraseDecl, DeclNode.toDecl, List.map_map]
  rfl

/-- The erased program is the same after the edit: the signature is all the erasure keeps. -/
theorem erase_program_apply (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d)
    (hm : e.d.members[e.j]? = some e.old) (hsig : eraseMember e.m' = eraseMember e.old.m) :
    erase (t.apply (.replaceMember e.i e.j e.m')).program = erase t.program := by
  rw [apply_replaceMember t e hd]
  unfold erase Tree.program
  simp only [List.map_map]
  apply map_setAt
  intro y hy
  rw [hd] at hy
  injection hy with hy
  subst hy
  simp only [Function.comp_def, eraseDecl_toDecl]
  congr 1
  apply map_setAt
  intro z hz
  rw [hm] at hz
  injection hz with hz
  subst hz
  show Stat.member (eraseMember e.m') = Stat.member (eraseMember e.old.m)
  rw [hsig]

theorem heads_apply (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d) :
    (t.apply (.replaceMember e.i e.j e.m')).decls.map (·.head) = t.decls.map (·.head) := by
  rw [apply_replaceMember t e hd]
  apply map_setAt
  intro y hy
  rw [hd] at hy
  injection hy with hy
  subst hy
  rfl

theorem findDeclNode_apply (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d) (id : Nat) :
    ((findDeclNode (t.apply (.replaceMember e.i e.j e.m')) id).map (·.head)) = (findDeclNode t id).map (·.head) := by
  rw [apply_replaceMember t e hd]
  unfold findDeclNode
  apply find?_setAt_map
  intro y hy
  rw [hd] at hy
  injection hy with hy
  subst hy
  exact ⟨rfl, rfl⟩

theorem findMemberNode_apply (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d)
    (hm : e.d.members[e.j]? = some e.old) (id : Nat) (h1 : id ≠ e.old.id) (h2 : id ≠ t.next) :
    ((findMemberNode (t.apply (.replaceMember e.i e.j e.m')) id).map memberProj) = (findMemberNode t id).map memberProj := by
  rw [apply_replaceMember t e hd]
  unfold findMemberNode
  simp only [List.map_findSome?]
  apply findSome?_setAt
  intro y hy
  rw [hd] at hy
  injection hy with hy
  subst hy
  simp only [Function.comp_def, Option.map_map]
  rw [find?_setAt_of_false]
  · rfl
  · simpa using h2.symm
  · intro z hz
    rw [hm] at hz
    injection hz with hz
    subst hz
    simpa using h1.symm

/-- **The body-edit rule, for every program and every edit.** After a body edit of the node `old`
at `(i, j)` to a new node `t.next` with the same signature, every fact other than the two nodes'
typed forms has the same rule as before: the same `Task`, so the same value and the same trace
under every oracle. The namer's facts by [`rulesOf_erase`](#) (the erased program is unchanged);
another node's typed form because it reads its own node, its owner's reference and the erased
program; a declaration's typed form because it reads the headers only. -/
theorem bodyEdit_rules_eq (cut : Cut) (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d)
    (hm : e.d.members[e.j]? = some e.old) (hsig : eraseMember e.m' = eraseMember e.old.m) :
    let t' := t.apply (.replaceMember e.i e.j e.m')
    (∀ f, ToyTree.rulesOf cut t' (.namer f) = ToyTree.rulesOf cut t (.namer f)) ∧
    (∀ id, ToyTree.rulesOf cut t' (.typedDecl id) = ToyTree.rulesOf cut t (.typedDecl id)) ∧
    (∀ id, id ≠ e.old.id → id ≠ t.next →
      ToyTree.rulesOf cut t' (.typedMember id) = ToyTree.rulesOf cut t (.typedMember id)) := by
  intro t'
  have herase : erase t'.program = erase t.program := erase_program_apply t e hd hm hsig
  refine ⟨fun f => ?_, fun id => ?_, fun id h1 h2 => ?_⟩
  · rw [rulesOf_namer, rulesOf_namer, herase]
  · rw [rulesOf_typedDecl, rulesOf_typedDecl, heads_apply t e hd, findDeclNode_apply t e hd]
  · rw [rulesOf_typedMember, rulesOf_typedMember, ← typedMemberOf_erase cut t'.program,
      ← typedMemberOf_erase cut t.program, herase, findMemberNode_apply t e hd hm id h1 h2]

/-- The facts a body edit leaves alone: everything but the replaced node's and the new node's
typed forms. -/
def keep (t : Tree) (e : Edited) : TFact → Bool
  | .typedMember id => id != e.old.id && id != t.next
  | _ => true

/-- `Same` for a body edit, under every oracle: the hypothesis of
[`Query.Revision.reuse_sound`](../../query/Query/Revision.lean) discharged for every program. -/
theorem bodyEdit_same (cut : Cut) (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d)
    (hm : e.d.members[e.j]? = some e.old) (hsig : eraseMember e.m' = eraseMember e.old.m) (ρ' : TFact → TValue) :
    Same (ToyTree.rulesOf cut t) (ToyTree.rulesOf cut (t.apply (.replaceMember e.i e.j e.m'))) ρ' (keep t e) := by
  obtain ⟨hn, hdl, hmem⟩ := bodyEdit_rules_eq cut t e hd hm hsig
  intro q hq
  cases q with
  | namer f => rw [hn]; exact ⟨rfl, rfl⟩
  | typedDecl id => rw [hdl]; exact ⟨rfl, rfl⟩
  | typedMember id =>
    simp only [keep, Bool.and_eq_true, bne_iff_ne, ne_eq] at hq
    rw [hmem id hq.1 hq.2]; exact ⟨rfl, rfl⟩

/-- **Keeping the run is sound.** The old revision's store agrees with its fixed point, the new
revision's rules are ranked: then re-validating any fact of the new revision from the kept store,
reusing every entry but the edited node's, returns the new fixed point's value and leaves a store
that agrees with it. [`reuse_sound`](../../query/Query/Revision.lean) with `Same` discharged by
`bodyEdit_same`: the model's statement that dotc may keep its run, its symbols and every other
statement's typed tree, and must redo the edited member's typed form, when a request asks for it. -/
theorem bodyEdit_kept_run_sound (cut : Cut) (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d)
    (hm : e.d.members[e.j]? = some e.old) (hsig : eraseMember e.m' = eraseMember e.old.m)
    (ρ ρ' : TFact → TValue) (r : TFact → Nat) (old : Memo TFact TValue) (rev : Nat)
    (hfixold : Fix (ToyTree.rulesOf cut t) ρ) (hfix : Fix (ToyTree.rulesOf cut (t.apply (.replaceMember e.i e.j e.m'))) ρ')
    (hr : Ranked (ToyTree.rulesOf cut (t.apply (.replaceMember e.i e.j e.m'))) ρ' r)
    (hold : AgreeM (ToyTree.rulesOf cut t) ρ old) :
    ∀ n q m, r q < n → AgreeM (ToyTree.rulesOf cut (t.apply (.replaceMember e.i e.j e.m'))) ρ' m →
      ∃ m', reval (ToyTree.rulesOf cut (t.apply (.replaceMember e.i e.j e.m'))) (keep t e) old rev n [] m q = (.ok (ρ' q), m') ∧
        AgreeM (ToyTree.rulesOf cut (t.apply (.replaceMember e.i e.j e.m'))) ρ' m' := by
  intro n q m hn hm'
  obtain ⟨m', h, a, _⟩ := reuse_sound _ _ ρ ρ' r (keep t e) old rev hfixold hfix hr hold
    (bodyEdit_same cut t e hd hm hsig ρ') n q [] m hn hm' (by simp)
  exact ⟨m', h, a⟩

/-- The owner's member set is a function of the signatures: unchanged by a body edit. This is the
invariant that makes dotc's re-index with the old symbols sound (§12 "Redone": the refined symbols
are the owner's members positioned in the old definition, and the re-index must find exactly them
again, `refined.size == olds.size && news.size == olds.size`, or the session is poisoned). -/
theorem bodyEdit_ownNames (t : Tree) (e : Edited) (hd : t.decls[e.i]? = some e.d)
    (hm : e.d.members[e.j]? = some e.old) (hsig : eraseMember e.m' = eraseMember e.old.m) (r : Ref) :
    ownNames (t.apply (.replaceMember e.i e.j e.m')).program r = ownNames t.program r := by
  rw [← ownNames_erase, erase_program_apply t e hd hm hsig, ownNames_erase]

/-- The classifier's `Body` verdict implies the theorem's hypotheses: a `replaceMember` whose old
and new members erase to the same signature. -/
theorem isBodyEdit_sound (t : Tree) (ed : Edit) (h : isBodyEdit t ed = true) :
    ∃ e : Edited, ed = .replaceMember e.i e.j e.m' ∧ t.decls[e.i]? = some e.d ∧ e.d.members[e.j]? = some e.old ∧
      eraseMember e.m' = eraseMember e.old.m := by
  cases ed with
  | replaceDecl _ _ => simp [isBodyEdit] at h
  | insertDecl _ _ => simp [isBodyEdit] at h
  | deleteDecl _ => simp [isBodyEdit] at h
  | replaceMember i j m' =>
    unfold isBodyEdit at h
    cases hd : t.decls[i]? with
    | none => simp [hd] at h
    | some d =>
      simp only [hd] at h
      cases hm : d.members[j]? with
      | none => simp [hm] at h
      | some old =>
        simp only [hm, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨⟨⟨hn, hs⟩, hdecl⟩, hdep⟩, -⟩, -⟩ := h
        refine ⟨⟨i, j, d, old, m'⟩, rfl, hd, hm, ?_⟩
        simp only [eraseMember, ← hdecl, hs, ↓reduceIte, ← hn, ← hdep]

/-! ## Witnesses by `decide`: the kept run on a space of programs and edits

The theorems above are about rules; what follows runs the kept run itself, on a space of small
programs and single-member body edits, and checks what §12 claims of dotc: nothing outside the
member is recomputed, the skipped member's later request answers as a fresh store does, the
diagnostics outside the member are unchanged. -/

/-- The kept run: every fact of the new tree except the edited node's re-validated from the old
store by trace, with the edited node's typed form left skipped (no entry), as dotc keeps the run
and makes the member a `SkippedStat`. -/
def keptRun (cut : Cut) (r : Rev) (e : Edit) : Rev :=
  let t' := r.tree.apply e
  let keepB : TFact → Bool := fun q => match q with | .typedMember id => id != r.tree.next | _ => true
  let m' := (revalAll (ToyTree.rulesOf cut t') keepB r.memo (r.rev + 1) fuel ((facts t').filter keepB) empty).2
  ⟨t', m', r.rev + 1⟩

/-- The error messages a fact's value carries: the toy's diagnostics, keyed by the fact that
produced them (dotc's provenance, §12 "Diagnostics"), not by a position. -/
def errsOfValue : Value → List String
  | .err m => [m]
  | .typed t => match t.ty with | .err m => [m] | _ => []
  | _ => []

def errsOf : TValue → List String
  | .v x => errsOfValue x
  | .member sig body => errsOfValue sig ++ (body.map errsOfValue).getD []
  | .bodies bs => bs.flatMap fun (_, ms) => ms.flatMap fun (_, v) => errsOfValue v

def diagnostics (m : Memo TFact TValue) (qs : List TFact) : List (TFact × String) :=
  qs.flatMap fun q => match m q with | some e => (errsOf e.value).map (q, ·) | none => []

/-- What the kept run must satisfy on `(p, e)`, `e` a body edit of `p`'s tree, from a validated
revision: (1) no rule ran; (2) every fact outside the edited node has its old value; (3) the
edited node is skipped; (4) its later request answers as it would from a fresh store, and the store
then agrees with a fresh run on every fact; (5) the diagnostics outside the member are those of
the old revision, keyed by fact. -/
def keptRunOk (cut : Cut) (p : Program) (e : Edit) : Bool :=
  let r := (Rev.ofProgram p).validateAll cut
  let t := r.tree
  let newQ : TFact := .typedMember t.next
  let oldQ : TFact := match e with
    | .replaceMember i j _ => ((t.decls[i]? >>= fun d => d.members[j]?).map fun mn => TFact.typedMember mn.id).getD newQ
    | _ => newQ
  let r' := keptRun cut r e
  let t' := r'.tree
  let outside' := (facts t').filter (· != newQ)
  let outside := (facts t).filter (· != oldQ)
  r'.computed.isEmpty &&
  outside'.all (fun q => (r'.memo q).map (·.value) == (r.memo q).map (·.value)) &&
  (r'.memo newQ).isNone &&
  (let (o, r'') := r'.ask cut newQ
   o == (targeted cut t' newQ).1 && r''.agreesWithFresh cut) &&
  diagnostics r'.memo outside' == diagnostics r.memo outside

/-- The body edits of a program's tree: each declared member replaced by one with another body
from a menu of paths. -/
def bodyEditsOf (p : Program) : List Edit :=
  let t := Tree.ofProgram p
  let names := p.flatMap fun d => d.members.map (·.name)
  let paths : List (List String) :=
    [["c"], ["q", "c"], ["l", "self"], ["o", "m"], ["three", "twice"], ["X", "x"]] ++ names.map ([·])
  t.decls.zipIdx.flatMap fun (d, i) => d.members.zipIdx.flatMap fun (mn, j) =>
    if mn.m.declared.isSome then
      (paths.eraseDups.filter (· != mn.m.path)).map fun path => Edit.replaceMember i j { mn.m with path }
    else []

/-- The space: the kernel's scenarios, the tier and companion programs, and the two-declaration
programs of [`ToySpace.menu`](ToySpace.lean), each with every body edit of `bodyEditsOf`. -/
def space : List (Program × Edit) :=
  let ps := ToyTree.programs ++ [tier1, tier2, tier3a, tier3b, caseCompanion] ++ ToySpace.programs.filter (·.length == 3)
  ps.flatMap fun p => (bodyEditsOf p).map (p, ·)

/-- Every edit of the space is a body edit by the classifier's test, less the requirement of a body
on both sides (the menu's declared members are mostly abstract, and the toy's facts do not read
`Deferred`). -/
def spaceIsBodyEdits : Bool :=
  space.all fun (p, e) => match e with
    | .replaceMember i j m' =>
      match (Tree.ofProgram p).decls[i]? >>= fun d => d.members[j]? with
      | some old => old.m.declared.isSome && eraseMember m' == eraseMember old.m
      | none => false
    | _ => false

def tiers : List Program := [tier1, tier2, tier3a, tier3b, caseCompanion]

def spaceOf (ps : List Program) : List (Program × Edit) := ps.flatMap fun p => (bodyEditsOf p).map (p, ·)

/-- **The kept run, on the kernel's scenarios and the tier programs** (241 body edits, scalac cut):
no rule runs, every fact outside the member keeps its value, the member is skipped and its request
answers as a fresh store does, the diagnostics outside it are unchanged. -/
theorem kept_run_scenarios :
    (spaceOf (ToyTree.programs ++ tiers)).all (fun (p, e) => keptRunOk .scalac p e) = true := by
  decide +kernel

/-- The whole space (the kernel's scenarios, the tiers and the two-declaration programs of
`ToySpace.menu`: 1,695 edits over the 7 scenario, 5 tier and 56 menu programs, both cuts), compiled: every edit is a body edit and
the kept run is right on each. -/
example : space.all (fun (p, e) => keptRunOk .scalac p e && keptRunOk .fine p e) = true := by native_decide
example : spaceIsBodyEdits = true := by native_decide

/-! ## The catalogue: what makes the rule unsound

Each is a theorem on an example. The features the toy lacks (a sealed parent's `children`, local
givens, default getters, annotations, a diagnostic's provenance against its position) are argued
from dotc in the note beside this file. -/

/-- (a) `tier1`'s `p` has an inferred type: `def p = q.c`. Editing its body to `q`. -/
def inferredEdit : Edit := .replaceMember 1 2 { name := "p", path := ["q"] }

/-- **(a) An inferred result type leaks.** The classifier refuses the edit (`ineligible`: "no
declared result type"), and rightly: the member's own type fact changes (`Int` to `C`), with it
the owner's typed form, and a kept run would reuse the old type, since none of the fact's recorded
deps changed; the kept store disagrees with a fresh run. -/
theorem inferred_type_leaks :
    isBodyEdit (Tree.ofProgram tier1) inferredEdit = false ∧
    keptRunOk .scalac tier1 inferredEdit = false ∧
    (let r' := ((Rev.ofProgram tier1).validateAll .scalac).edit .scalac inferredEdit
     r'.changed.contains (.namer (.mem (cls "C") "p")) ∧ r'.changed.contains (.typedDecl 1) ∧
     r'.agreesWithFresh .scalac = true) := by
  decide

/-- The tree's rules with `inline` members: a caller's typed form splices the inlinee's body
(I28: a caller reads the typed body, not the signature). A member whose path starts with a
declared `inline` member of its own class, with a body, is typed as the inlinee's path followed by
the rest of its own; every other fact is as in [`ToyTree.rulesOf`](ToyTree.lean). -/
def rulesOfInline (cut : Cut) (t : Tree) (inl : List String) : Rules TFact TValue
  | .typedMember id =>
    match findMemberNode t id with
    | some (d, m) =>
      match m.m.path with
      | first :: rest =>
        match d.members.find? fun mn => mn.m.name == first && mn.m.name ∈ inl && mn.m.declared.isSome && !mn.m.path.isEmpty with
        | some callee =>
          if m.m.declared.isSome then do
            let sig ← askNamer (.mem d.ref m.m.name)
            let body ← lift (typePath cut t.program d.ref (callee.m.path ++ rest))
            pure (.member sig (some body))
          else ToyTree.rulesOf cut t (.typedMember id)
        | none => ToyTree.rulesOf cut t (.typedMember id)
      | [] => ToyTree.rulesOf cut t (.typedMember id)
    | none => ToyTree.rulesOf cut t (.typedMember id)
  | q => ToyTree.rulesOf cut t q

/-- `class C { def c: Int; inline def q: C = q; def s: Int = q.c }`. -/
def inlineToy : Program := [int,
  { name := "C", stats := [ToyKernel.m "c" "Int",
      .member { name := "q", declared := some "C", path := ["q"] },
      .member { name := "s", declared := some "Int", path := ["q", "c"] }] }]

/-- `q`'s body becomes `c`. -/
def inlineEdit : Edit := .replaceMember 1 1 { name := "q", declared := some "C", path := ["c"] }

/-- **(b) An `inline` body leaks into its callers' typed forms.** The edit is a body edit by the
classifier's syntactic test, and no namer fact changes (the signature is the same, so `q`'s type
and `C`'s members are); but `s`'s typed form, a fact outside `q`'s node, changes from `q.c : Int`
to `c.c`, an error, because it holds `q`'s body inlined. Under the rules without `inline` the kept
run is right on the same edit. `BodyEdit.ineligible` refuses `Inline | Transparent | Macro`. -/
theorem inline_body_leaks :
    let t := Tree.ofProgram inlineToy
    let t' := t.apply inlineEdit
    let f := (fresh (rulesOfInline .scalac t ["q"]) 0 fuel (facts t)).2
    let f' := (fresh (rulesOfInline .scalac t' ["q"]) 0 fuel (facts t')).2
    isBodyEdit t inlineEdit = true ∧
    ((facts t').filter fun q => match q with | .namer _ => true | _ => false).all
      (fun q => (f' q).map (·.value) == (f q).map (·.value)) = true ∧
    (f (.typedMember 4)).map (·.value) = some (.member (ty (.ref (cls "Int"))) (some (ty (.ref (cls "Int"))))) ∧
    (f' (.typedMember 4)).map (·.value) =
      some (.member (ty (.ref (cls "Int"))) (some (ty (.err "value c is not a member of Int")))) ∧
    keptRunOk .scalac inlineToy inlineEdit = true := by
  decide

/-- `object A { export B.{b}; def a: Int }; object B { def b: Int; def b2: Int }`, and the same with
the export widened to `B.*`: a change inside `A`'s template body that is not a member's body. -/
def exportToy : Program := [int,
  { obj := true, name := "A", stats := [.export "B" (some ["b"]), ToyKernel.m "a" "Int"] },
  { obj := true, name := "B", stats := [ToyKernel.m "b" "Int", ToyKernel.m "b2" "Int"] }]

def exportToyWide : Program := [int,
  { obj := true, name := "A", stats := [.export "B" none, ToyKernel.m "a" "Int"] },
  { obj := true, name := "B", stats := [ToyKernel.m "b" "Int", ToyKernel.m "b2" "Int"] }]

/-- **(g) A template body is not a right-hand side.** An export is a statement of the class, kept
by the erasure (`eraseDecl_exports`), so the two programs do not erase to the same one and
[`rulesOf_erase`](#) says nothing; and indeed the class's member set, a namer fact, changes. The
tree has no exports at all (`DeclNode.toDecl` keeps members only), so this is at the namer, under
the fine cut, which has exports. `BodyEdit.editedMember` descends into a template's statements and
returns a `ValOrDefDef` only, so an export, an import or a class header differs outside any
right-hand side and the run is fresh. -/
theorem export_is_not_a_body :
    erase exportToyWide ≠ erase exportToy ∧
    (run .fine exportToy [obj "A", obj "B"]).2 (.decls (obj "A")) = some (.names ["a", "b"]) ∧
    (run .fine exportToyWide [obj "A", obj "B"]).2 (.decls (obj "A")) = some (.names ["a", "b", "b2"]) := by
  decide

/-- **(d) A body cannot define an implicit.** In the toy the implicit views a path may go through
are the program's implicit classes, read from the headers (`findImplicit` scans `p`); a member's
body is a path and declares nothing, so this is a special case of [`rulesOf_erase`](#): the
implicit classes of `erase p` are those of `p`. In dotc a `given` local to a body is in no
`ContextualImplicits` of another member and in no type's implicit scope. -/
theorem local_implicit_cannot_leak (cut : Cut) (p : Program) (r : Ref) (n : String) :
    findImplicit cut (erase p) r n (erase p) = findImplicit cut p r n p :=
  findImplicit_erase' cut p r n

/-- **(h) Another member's lookups resolve as before.** What a path step finds (`lookupIn`, by the
member sets through the parents, and `findImplicit`) is a function of the erased program: no
resolution in another member reads a declared member's body. dotc's overloading resolution reads
the alternatives' infos, which for declared result types are the signatures'. -/
theorem lookup_unchanged (cut : Cut) (p : Program) (fuel : Nat) (r : Ref) (n : String) :
    lookupIn cut (erase p) fuel r n = lookupIn cut p fuel r n :=
  lookupIn_erase cut p fuel r n

end ScalaTypes.ToyBodyEdit
