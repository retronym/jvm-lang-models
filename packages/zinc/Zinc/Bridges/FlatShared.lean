import Zinc.Bridges.FlatRules
import Zinc.Bridges.HierShared
import ScalaTypes.Members
/-!
# `Flat`'s toy Scala, embedded in the shared Scala semantics

`Flat` extends `Hier`'s language with member kinds (`val`, `var`, `lazy val`), deferred and private
members, traits, objects, `final` and abstract classes, and runs a class's refchecks and codegen
against its ancestors. Its programs are lowered to the shared syntax (`Flat.declToScala`), and its
stored linearization *is* the shared walk over headers (`Scala.linH`). This file proves, for every
program:

* **linearization** (`lin_eq_shared`): each class's stored linearization (`Iface.lin`), with type
  arguments, is `Scala.lin` over whole declarations (both empty when the walk fails);
* **selection** (`sel_eq_shared`): a selection `c.n` resolves, along the stored linearization
  and seen from `c` by the shared `asSeenFrom`, to `Scala.lookup`'s member, provided `c` itself
  does not declare `n` private (`Scala.lookup` is `c`'s view of itself, which sees its own private
  members; a client does not).

Refchecks stay `Flat`'s own: they read finer keys than `Scala.Members` (an ancestor's own member,
whether it declares a name, whether deferred), which is the point of the PoC's rule table. They are
compared with `Scala.Members.errors` over `FlatRules`' 216,000 programs, as calibration
(`lake exe exhaustive flatshared [2.12|2.13|3]`): an override (`resultType`, `stable`,
`lazyMismatch`), a conflict (`conflicting`, `accidental`), an unimplemented abstract member
(`needsAbstract`). A `final` parent is not in `Members` (scalac checks it in the typer), so it is
left out.

Results, over the 192,000 programs without a `var`:

| | 2.12 | 2.13 | 3 |
|---|---|---|---|
| linearization agrees | 192,000 | 192,000 | 192,000 |
| selections agree | 192,000 | 192,000 | 192,000 |
| each class compiles under both, or fails under both | 162,320 | 117,520 | 183,488 |
| the same errors, by kind and class | 137,456 | 84,288 | 153,952 |

The first two rows are now `lin_eq_shared` and `sel_eq_shared` (no class of the space declares a
selected member private). `Flat`'s refchecks are closest to Scala 3's. The named exclusions, where
`Flat` and `Members` are known to differ and `Members` is not widened:

* **`var`** (`hasVar`): `Members` has no `var`; programs in which the trait declares one are
  counted apart.
* **Scala 2.13 re-checks a pair a parent already has**, and reports it again in the subclass;
  `Flat`, like 2.12 and 3, checks it once (scalac's `OverridingPairs`; `Scala.Members.recheck`).
* **Scala 3's direct-parent rule, 320 programs:** `trait A extends M` re-declares `m` abstract over
  `M`'s concrete `m`, `B extends A`, `C extends B with M`. dotc accepts `C`, because `M` is a direct
  parent; `Flat` lets the abstract declaration win, as javac does. Neither is the specification,
  under which a concrete definition always overrides an abstract one (`Scala.Members.concreteS3`).
* **Which errors a broken class reports** differs more than whether it compiles: `Flat` checks
  inherited conflicts only for names the class does not declare.

Checking this comparison found two gaps in the shared semantics, both fixed in `Scala.Members` and
pinned by witnesses there: an abstract member and a concrete one of an incompatible type through
different parents (both compilers reject), and Scala 3's re-abstraction by a trait (track-s.md, 13 Oct).
-/

open Query

namespace Zinc.Flat.Shared

open Zinc.Hier (Cls Name Ty)

theorem _root_.Zinc.Hier.Cls.ofName?_name (c : Cls) : Cls.ofName? c.name = some c := by
  cases c <;> rfl

theorem _root_.Zinc.Hier.Cls.name_of_ofName? {s : String} {c : Cls} (h : Cls.ofName? s = some c) :
    c.name = s := by
  simpa using List.find?_some h

theorem _root_.Zinc.Hier.Cls.name_inj {c d : Cls} (h : c.name = d.name) : c = d := by
  have := Cls.ofName?_name c; rw [h, Cls.ofName?_name] at this; exact (Option.some.inj this).symm

theorem _root_.Zinc.Hier.Name.str_inj {n n' : Name} (h : n.str = n'.str) : n = n' := by
  cases n <;> cases n' <;> first | rfl | exact absurd h (by decide)

def classes : List Cls := [.A, .B, .M, .C, .X, .Y, .Z]

/-- A `Flat` declaration in the shared syntax. -/
def D (src : Cls → Src) (c : Cls) : Scala.Decl := declToScala c (src c).decl

def program (src : Cls → Src) : Scala.Program :=
  classes.map fun c =>
    if (src c).decl.kind == .obj then { name := c.name, obj := some (D src c) }
    else { name := c.name, cls := some (D src c) }

/-- The program's environment, reading an object where there is no class (`need` asks for the
class, and a `Flat` object extends classes like one). -/
def env (src : Cls → Src) : Scala.Env
  | .decl n _ => (Cls.ofName? n).map fun c => { decl := D src c }
  | .header n => (Cls.ofName? n).map fun c => (D src c).header
  | .member n m => (Cls.ofName? n).bind fun c => (D src c).member m

theorem env_consistent (src : Cls → Src) : Scala.Consistent (env src) := by
  refine ⟨fun n => ?_, fun n m => ?_⟩ <;>
  · simp only [env]; cases Cls.ofName? n <;> rfl

/-- Run a shared-semantics computation over the program. -/
def runOn (src : Cls → Src) {α : Type} (m : Scala.M α) : Except String α := Scala.ex (env src) m

/-! ## The stored linearization is the shared one -/

/-- The interfaces of a clean build. -/
def cleanI (src : Cls → Src) (c : Cls) : Iface := (clean src c).iface

/-- The declarations of `src`, with nothing stored. -/
def declsI (src : Cls → Src) (c : Cls) : Iface := ⟨(src c).decl, []⟩

theorem cleanI_eq (src : Cls → Src) (c : Cls) :
    cleanI src c = ⟨(src c).decl, ((linOf c (D src c).header).run (answer (declsI src))).drop 1⟩ := by
  have : declEnv Finset.univ (lowerAll src) (fun _ => ⟨{}, []⟩) = declsI src := by
    funext v; simp [declEnv, declsI, lowerAll]
  simp only [cleanI, clean, group_iface, matIface, lowerAll, D, this]

theorem cleanI_decl (src : Cls → Src) (c : Cls) : (cleanI src c).decl = (src c).decl := by
  rw [cleanI_eq]

/-- `toQ` answers the walk's `header` queries as the program's environment does. -/
theorem through_agrees (src : Cls → Src) :
    ∀ q, Scala.Heady q → Query.Task.Env.through toQ (answer (declsI src)) q = env src q
  | .header s, _ => by
    simp only [Query.Task.Env.through, toQ, env]
    cases h : Cls.ofName? s <;> rfl

theorem run_linOf (src : Cls → Src) (c : Cls) (h : Scala.Header) :
    (linOf c h).run (answer (declsI src)) = ofLin (Scala.ex (env src) (Scala.linH Scala.fuel (c.name, h))) := by
  simp only [linOf, Task.bind_eq, Task.run_bind, Task.pure_eq, Task.run_pure, Task.run_interp]
  congr 1
  exact Task.run_congr _ _ _ fun q hq =>
    through_agrees src q (Scala.asks_linH_of (fun _ => trivial) _ _ _ q hq)

theorem ex_need (src : Cls → Src) (c : Cls) : Scala.ex (env src) (Scala.need c.name) = .ok (D src c) := by
  simp only [Scala.need, Scala.ex_map, Scala.ex_needView, env, Cls.ofName?_name]
  rfl

/-- The shared linearization of a related list of headers, by class. -/
theorem ofLin_rel (src : Cls → Src) : ∀ (l₁ : List Scala.Anc) (l₂ : List ((String × Scala.Header) × List Scala.Ty)),
    Scala.RelL (Scala.RelAnc (env src)) l₁ l₂ →
      (ofLin (.ok l₂)).map (fun (e, ts) => (D src e, ts)) = l₁
  | [], [], _ => rfl
  | (d, ts) :: rest₁, (h, us) :: rest₂, ⟨⟨⟨hh, v, hv, hvd⟩, hts⟩, hl⟩ => by
    simp only at hh hv hvd hts
    simp only [env] at hv
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
    simp only at hvd
    subst hvd
    have hname : h.2.name = c.name := by rw [hh]; rfl
    have ih := ofLin_rel src rest₁ rest₂ hl
    simp only [ofLin] at ih ⊢
    simp only [List.filterMap_cons, hname, Cls.ofName?_name, Option.map_some, List.map_cons, ih, hts]

/-- A successful linearization starts with the class, applied to its own parameters. -/
theorem linWith_head {N : Type} (nd : Scala.Node N) (e : Scala.Env) (k : Nat) (d : N)
    (l : List (N × List Scala.Ty)) (h : Scala.ex e (Scala.linWith nd (k + 1) d) = .ok l) :
    ∃ acc, l = (d, (List.range (nd.tparams d)).map (Scala.Ty.tp [nd.name d])) :: acc := by
  simp only [Scala.linWith, Scala.ex_bind, Scala.ex_pure] at h
  split at h
  · exact ⟨_, (Except.ok.inj h).symm⟩
  · cases h

/-- **The stored linearization of a class, as `Scala.lin` gives it**, the class first: the shared
walk over whole declarations, mapped to `Flat`'s classes. -/
theorem lin_cls (src : Cls → Src) (c : Cls) (l₁ : List Scala.Anc)
    (h : Scala.ex (env src) (Scala.lin Scala.fuel (D src c)) = .ok l₁) :
    ((c, selfArgs c (src c).decl) :: (cleanI src c).lin).map (fun (e, ts) => (D src e, ts)) = l₁ := by
  have hf := Scala.lin_fine (env src) (env_consistent src) Scala.fuel (D src c) (c.name, (D src c).header)
    ⟨rfl, { decl := D src c }, by simp only [env, Cls.ofName?_name]; rfl, rfl⟩
  rw [h] at hf
  revert hf
  cases h₂ : Scala.ex (env src) (Scala.linH Scala.fuel (c.name, (D src c).header)) with
  | error _ => intro hf; exact hf.elim
  | ok l₂ =>
    intro hf
    have hl := ofLin_rel src l₁ l₂ hf
    obtain ⟨acc, rfl⟩ := linWith_head Scala.Node.header _ 7 _ l₂ h₂
    rw [cleanI_eq, run_linOf, h₂]
    rw [← hl]
    simp only [ofLin, List.filterMap_cons, Scala.Node.header, header_declToScala, D, Cls.ofName?_name,
      Option.map_some, List.drop_succ_cons, List.drop_zero, List.map_cons, selfArgs]

def toyLin (src : Cls → Src) (c : Cls) : List (String × List Scala.Ty) :=
  (cleanI src c).lin.map fun (p, ts) => (p.name, ts)

/-- The shared linearization of `c`, without `c`, as `(class, type arguments)`. -/
def sharedLin (src : Cls → Src) (c : Cls) : Except String (List (String × List Scala.Ty)) :=
  runOn src do
    let d ← Scala.need c.name
    let l ← Scala.lin Scala.fuel d
    pure ((l.drop 1).map fun (a, ts) => (a.name, ts))

/-- **`Flat`'s stored linearization is the shared one**, for every program and class (both empty
when the walk fails: a cycle, or one too deep). -/
theorem lin_eq_shared (src : Cls → Src) (c : Cls) :
    toyLin src c = match sharedLin src c with | .ok l => l | .error _ => [] := by
  simp only [sharedLin, runOn, Scala.ex_bind, ex_need]
  cases h : Scala.ex (env src) (Scala.lin Scala.fuel (D src c)) with
  | ok l₁ =>
    simp only [Scala.ex_pure]
    rw [← lin_cls src c l₁ h]
    simp only [toyLin, List.map_cons, List.drop_succ_cons, List.drop_zero, List.map_map]
    rfl
  | error s =>
    simp only
    have hf := Scala.lin_fine (env src) (env_consistent src) Scala.fuel (D src c) (c.name, (D src c).header)
      ⟨rfl, { decl := D src c }, by simp only [env, Cls.ofName?_name]; rfl, rfl⟩
    rw [h] at hf
    revert hf
    cases h₂ : Scala.ex (env src) (Scala.linH Scala.fuel (c.name, (D src c).header)) with
    | ok _ => intro hf; exact hf.elim
    | error _ =>
      intro _
      simp only [toyLin, cleanI_eq, run_linOf, h₂, ofLin, List.drop_nil, List.map_nil]

/-! ## Selections are the shared lookup -/

@[simp] theorem D_name (src : Cls → Src) (e : Cls) : (D src e).name = e.name := rfl
@[simp] theorem memToScala_name (e : Cls) (n : Name) (mm : Mem) : (memToScala e n mm).name = n.str := rfl
@[simp] theorem memToScala_fieldOnly (e : Cls) (n : Name) (mm : Mem) :
    (memToScala e n mm).fieldOnly = false := rfl
@[simp] theorem memToScala_priv (e : Cls) (n : Name) (mm : Mem) : (memToScala e n mm).priv = mm.priv := rfl

/-- A declaration's own member, in the shared syntax. -/
theorem member_D (src : Cls → Src) (e : Cls) (n : Name) :
    (D src e).member n.str = ((src e).decl.decls.lookup n).map (memToScala e n) := by
  simp only [D, declToScala, Scala.Decl.member]
  induction (src e).decl.decls with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨n', mm⟩ := p
    simp only [List.map_cons, List.find?_cons, List.lookup_cons, memToScala_name, memToScala_fieldOnly,
      Bool.not_false, Bool.and_true]
    by_cases hn : n = n'
    · subst hn; simp
    · have : (n'.str == n.str) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hn (Name.str_inj h).symm
      have h' : (n == n') = false := by simp [hn]
      simp only [this, h']
      exact ih

/-- What a class sees of an ancestor's member `n` (`Scala.hits`) is `Flat`'s `own`, unless the
class itself declares `n` private. -/
theorem visible_D (src : Cls → Src) (c e : Cls) (n : Name)
    (hpriv : ∀ mm, (src c).decl.decls.lookup n = some mm → mm.priv = false) :
    ((D src e).member n.str).filter (fun m => !m.priv || (D src e).name == c.name) =
      (ownD (src e).decl n).map (memToScala e n) := by
  rw [member_D]
  simp only [ownD]
  cases hl : (src e).decl.decls.lookup n with
  | none => rfl
  | some mm =>
    simp only [Option.map_some, Option.filter_some, memToScala_priv, D_name]
    by_cases hce : e = c
    · subst hce
      have := hpriv mm hl
      simp [this]
    · have : (e.name == c.name) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => hce (Cls.name_inj h)
      simp only [this, Bool.or_false]
      by_cases hp : mm.priv <;> simp [hp]

theorem filterMap_head? {α β : Type} (f : α → Option β) :
    ∀ l : List α, (l.filterMap f).head? = (l.find? fun x => (f x).isSome).bind f
  | [] => rfl
  | x :: rest => by
    simp only [List.filterMap_cons, List.find?_cons]
    cases h : f x
    · simp only [Option.isSome_none]; exact filterMap_head? f rest
    · simp [h]

/-- The first element with a property `Q` that only depends on a key is the first with its key. -/
theorem find?_key {α β : Type} [DecidableEq β] (key : α → β) (Q : α → Bool)
    (hQ : ∀ x y, key x = key y → Q x = Q y) :
    ∀ (l : List α) (x : α), l.find? Q = some x → l.find? (fun y => key y = key x) = some x
  | [], _, h => by simp at h
  | y :: rest, x, h => by
    simp only [List.find?_cons] at h ⊢
    cases hy : Q y
    · simp only [hy] at h
      have hx := List.find?_some h
      have : key y ≠ key x := fun he => by rw [hQ y x he, hx] at hy; cases hy
      simp only [this, decide_false]
      exact find?_key key Q hQ rest x h
    · simp only [hy, Option.some.injEq] at h
      subst h; simp

/-- `asSeenFrom` of a parameter of `o` reads only `o`'s base type. -/
theorem seenFromN_tp (self o : String) (L L' : List (String × List Scala.Ty)) (i : Nat)
    (h : L.find? (fun x => [x.1] == [o]) = L'.find? (fun x => [x.1] == [o])) :
    Scala.seenFromN self L o (.tp [o] i) = Scala.seenFromN self L' o (.tp [o] i) := by
  have ha : L.any (fun x => [x.1] == [o]) = L'.any (fun x => [x.1] == [o]) := by
    have h₁ := congrArg Option.isSome h
    rwa [List.isSome_find?, List.isSome_find?] at h₁
  show AsSeenFrom.asf (Scala.namedWorld self L) (.this [self]) [o] (.tp [o] i) =
    AsSeenFrom.asf (Scala.namedWorld self L') (.this [self]) [o] (.tp [o] i)
  simp only [AsSeenFrom.asf, AsSeenFrom.Subst.bind, Scala.Ty.bind, AsSeenFrom.leafAsSeen, AsSeenFrom.hit,
    AsSeenFrom.atHit, Scala.namedWorld, AsSeenFrom.Leafy.cls, AsSeenFrom.Leafy.kind, ha, h]

/-- A toy type of `o`, seen from `self`, reads only `o`'s base type. -/
theorem seenFromN_toScala (self : String) (o : Cls) (L L' : List (String × List Scala.Ty)) (t : Ty)
    (h : L.find? (fun x => [x.1] == [o.name]) = L'.find? (fun x => [x.1] == [o.name])) :
    Scala.seenFromN self L o.name (Ty.toScala o t) = Scala.seenFromN self L' o.name (Ty.toScala o t) := by
  cases t
  · rfl
  · rfl
  · exact seenFromN_tp self o.name L L' 0 h
  · rfl

/-- The type a selection `c.n` has in the shared semantics: the first member named `n` along
`c`'s linearization, seen from `c` (`Scala.lookup`). -/
def sharedSel (src : Cls → Src) (c : Cls) (n : Name) : Except String (Option Scala.Ty) :=
  runOn src (Scala.lookup Scala.fuel c.name n.str)

/-- The type a client's selection `c.n` has in `Flat`'s clean build. -/
def toySel (src : Cls → Src) (c : Cls) (n : Name) : Option Scala.Ty :=
  lookupFlat c (flatOf (cleanI src) c n)

/-- **A selection in `Flat` is the shared lookup**, for every program in which the linearization
succeeds, unless the receiver declares the name private (a client then reaches an inherited
member; `Scala.lookup`, the class's view of itself, the private one). -/
theorem sel_eq_shared (src : Cls → Src) (c : Cls) (n : Name)
    (hpriv : ∀ mm, (src c).decl.decls.lookup n = some mm → mm.priv = false)
    (t : Option Scala.Ty) (h : sharedSel src c n = .ok t) : toySel src c n = t := by
  simp only [sharedSel, runOn, Scala.lookup, Scala.ex_bind, ex_need] at h
  revert h
  cases hl : Scala.ex (env src) (Scala.lin Scala.fuel (D src c)) with
  | error _ => intro h; cases h
  | ok l₁ =>
    intro h
    simp only [Scala.ex_pure, Except.ok.injEq] at h
    subst h
    have hcls := lin_cls src c l₁ hl
    subst hcls
    -- the class's linearization, by class
    generalize hLc : (c, selfArgs c (src c).decl) :: (cleanI src c).lin = Lc
    have hflat : flatOf (cleanI src) c n =
        Lc.filterMap fun (e, a) => (ownD (src e).decl n).map fun mm => (e, a, mm) := by
      rw [← hLc]; simp only [flatOf, own, cleanI_decl]
    have hhits : Scala.hits (Lc.map fun (e, ts) => (D src e, ts)) n.str =
        (flatOf (cleanI src) c n).map fun (e, a, mm) => ((D src e, a), memToScala e n mm) := by
      rw [hflat, List.map_filterMap]
      have hself : ((Lc.map fun (e, ts) => (D src e, ts)).head?.map (·.1.name)).getD "" = c.name := by
        rw [← hLc]; simp
      simp only [Scala.hits, hself, List.filterMap_map]
      apply List.filterMap_congr
      intro ⟨e, a⟩ _
      have := visible_D src c e n hpriv
      simp only [Function.comp, Scala.Decl.member] at this ⊢
      rw [this]
      cases ownD (src e).decl n <;> rfl
    rw [hhits, List.head?_map, Option.map_map]
    unfold toySel lookupFlat
    rw [hflat, filterMap_head?]
    cases hx : Lc.find? (fun x => ((ownD (src x.1).decl n).map fun mm => (x.1, x.2, mm)).isSome) with
    | none => rfl
    | some x =>
      obtain ⟨e, a⟩ := x
      simp only [Option.bind_some]
      cases ho : ownD (src e).decl n with
      | none =>
        have := List.find?_some hx
        simp [ho] at this
      | some mm =>
        simp only [Option.map_some, Function.comp, seen, Scala.seenFrom, D_name]
        congr 1
        show _ = Scala.seenFromN c.name _ e.name (Ty.toScala e mm.ty)
        apply seenFromN_toScala
        -- the owner's first entry by name is the one found
        have hk := find?_key (fun x : Cls × List Scala.Ty => x.1.name)
          (fun x => ((ownD (src x.1).decl n).map fun mm => (x.1, x.2, mm)).isSome)
          (fun x y hxy => by simp [Cls.name_inj hxy]) Lc (e, a) hx
        simp only [List.map_map, List.find?_map, Function.comp_def, List.find?_cons, List.find?_nil]
        simp only [D_name, List.cons_beq_cons, Bool.and_true, beq_self_eq_true]
        have hk' : Lc.find? (fun x => x.1.name == e.name) = some (e, a) := by
          exact hk
        rw [hk']; rfl

/-! ## Refchecks, by kind (calibration) -/

/-- The selections of `d`'s body, the toy's resolved types against the shared ones. -/
def selAgrees (src : Cls → Src) (d : Cls) : Bool :=
  ((src d).body.zip (clean src d).descs).all fun ((c, n), (_, t, _)) =>
    sharedSel src c n == .ok t

/-- An error, by kind. -/
inductive EK | ovr | cfl | abs | other (s : String)
  deriving DecidableEq, Repr

def toyKinds (src : Cls → Src) (c : Cls) : List EK :=
  ((clean src c).errs.filterMap fun
    | .override _ => some EK.ovr | .conflict _ => some .cfl | .abstract _ => some .abs
    | .final _ => none).eraseDups

def sharedKinds (src : Cls → Src) (dl : Scala.Dialect := .s213) : Except String (List (String × EK)) := do
  let es ← Scala.Members.errors dl (program src)
  pure (es.map fun e => (e.cls, match e.kind with
    | .resultType | .stable | .lazyMismatch => EK.ovr
    | .conflicting | .accidental => .cfl
    | .needsAbstract => .abs
    | k => .other k.name)).eraseDups

def sameSet (a b : List EK) : Bool := a.all b.contains && b.all a.contains

def errsAgree (src : Cls → Src) (dl : Scala.Dialect := .s213) : Bool :=
  match sharedKinds src dl with
  | .ok es => classes.all fun c =>
      sameSet (toyKinds src c) ((es.filter (·.1 == c.name)).map (·.2))
  | .error _ => false

def linAgrees (src : Cls → Src) : Bool :=
  classes.all fun c => sharedLin src c == .ok (toyLin src c)

/-- The named exclusion: the trait declares a `var`, which `Members` does not have. -/
def hasVar (k : Cfg) : Bool := k.oM == .var

/-- Per program: linearization, selections (both theorems now), refchecks. -/
def check (k : Cfg) (dl : Scala.Dialect := .s213) : Bool × Bool × Bool :=
  let src := k.src
  (linAgrees src, classes.all (selAgrees src), errsAgree src dl)

/-- Does each class compile? The toy's verdict (no error, a `final` parent included) against the
shared one. This is what an incremental build must reproduce; which errors are reported matters
less. -/
def verdictAgrees (src : Cls → Src) (dl : Scala.Dialect := .s213) : Bool :=
  match sharedKinds src dl with
  | .ok es => classes.all fun c =>
      ((clean src c).errs.filter (fun | .final _ => false | _ => true)).isEmpty ==
        (es.filter (·.1 == c.name)).isEmpty
  | .error _ => false

/-- Where refchecks disagree: the classes and kinds each side reports, the toy's first. -/
def errPattern (k : Cfg) (dl : Scala.Dialect) : String :=
  let toy := classes.flatMap fun c => (toyKinds k.src c).map fun e => (c.name, e)
  match sharedKinds k.src dl with
  | .ok sh => s!"{repr toy} vs {repr sh}"
  | .error e => s!"error {e}"

end Zinc.Flat.Shared
