import IncComp.General
import Scala.Catalogue
import Query.Interp
/-!
# Track B4: Zinc-clean implies binary compatible

**The front end.** Scala lowering (`packages/scala/Scala/Lower.lean`) as an `XCompiler` (`General.lean`):

* a unit is a source unit, named;
* its task is `Scala.lowerSrc`, its queries renamed into the framework's shape (`decl n isObj` asks
  unit `n` for one side of its interface);
* its output is the unit's source interface (its class and object declarations) together with
  its lowered classfiles.

The interface is the declaration, so it is source-determined: the explicit-interface case of T3b.

Every query is answered as if the definition were in the same compiler run (`View.inRun = true`).
That is faithful for Scala 2.12 and 2.13, whose lowering ignores `inRun`. For Scala 3, separate
compilation differs (F6: a trait's `$init$`), which is a failure of compositionality
(`packages/scala/Scala/Facts.lean`), not something a key repairs.

**A sound bridge** (`searched`): a key per traced query, its hash the declaration it read. It meets
the obligations (`searched_obligations`), so the hypothesis of the theorem below is satisfiable.

**The theorem**, for any `XCompiler` meeting the obligations whose interfaces are source-determined
(`untouched_eq_clean`, in `General.lean` with the explicit-interface T3b it rests on). After an edit, if Zinc's loop stops and a unit `c` was never in a round
(`c ∉ recompiled …`), then `c`'s old output equals its output in the clean build of the new sources.
For lowering, the old classfiles of `c` next to the new library link exactly as a fresh build
does (`after_eq_fresh`), so `Jvm.Compatible` holds whenever the fresh build links
(`compatible_of_untouched`).

**The converse fails** (`gap_witness`): a concrete method added to a trait is binary compatible
for a class mixing the trait in (it links, and selects the trait's default method), but the class's
lowered classfile changes (a fresh build adds a mixin forwarder). So every sound bridge must have
Zinc recompile it (`must_recompile`). MiMa reports nothing here: the gap between `Compatible` and
Zinc-clean is exactly such edits.
-/

open Query IncComp


/-! ## Scala lowering as an `XCompiler` -/

namespace Links.ZincBridge

open Scala

/-- The framework's queries: unit `n`, and which side (`true`: the object). -/
abbrev FQ := String × Bool

abbrev FAns : FQ → Type := fun _ => Option View

/-- A query of the shared layer as the framework's: `decl n o` asks unit `n` for one side;
`header n` and `member n m` are projections of `n`'s class side, so they ask for it. -/
def fq : Scala.Q → FQ
  | .decl n o => (n, o)
  | .header n => (n, false)
  | .member n _ => (n, false)

/-- The answer to `q`, from the side `fq q` reads. -/
def fromSide : (q : Scala.Q) → FAns (fq q) → Scala.Ans q
  | .decl .., v => v
  | .header _, v => v.map (·.decl.header)
  | .member _ m, v => v.bind (·.decl.member m)

/-- Rename lowering's queries into the framework's shape. -/
def tr {α : Type} : Query.Task Scala.Q Scala.Ans α → Query.Task FQ FAns α :=
  Query.Task.rename fq fromSide

/-- An environment in the framework's shape, read by lowering. -/
def back (e : (q : FQ) → FAns q) : (q : Scala.Q) → Scala.Ans q := fun q => fromSide q (e (fq q))

theorem run_tr {α : Type} (e : (q : FQ) → FAns q) (t : Query.Task Scala.Q Scala.Ans α) :
    (tr t).run e = t.run (back e) :=
  Query.Task.run_rename _ _ e t

theorem trace_tr {α : Type} (e : (q : FQ) → FAns q) (t : Query.Task Scala.Q Scala.Ans α) :
    (tr t).trace e = (t.trace (back e)).map fq :=
  Query.Task.trace_rename _ _ e t

/-- A unit's interface: its class and object declarations, if it exists. -/
abbrev Iface := Option (Option Decl × Option Decl)

structure Out where
  iface : Iface
  classes : Except String (List ClassOut)
  deriving DecidableEq

def ifaceSrc : Option Scala.Src → Iface
  | none => none
  | some s => some (s.cls, s.obj)

/-- One side of a unit's interface: the hash of a key, and the answer to a query. -/
def side (I : String → Iface) (q : FQ) : Option Decl :=
  (I q.1).bind fun co => if q.2 then co.2 else co.1

def answer (I : String → Iface) (q : FQ) : FAns q := (side I q).map fun d => { decl := d }

def unit (dl : Dialect) : Option Scala.Src → Query.Task FQ FAns Out
  | none => .pure ⟨none, .error "absent"⟩
  | some s => (tr (lowerSrc dl s).run).bind fun r => .pure ⟨some (s.cls, s.obj), r⟩

theorem iface_unit (dl : Dialect) (s : Option Scala.Src) (e : (q : FQ) → FAns q) :
    ((unit dl s).run e).iface = ifaceSrc s := by
  cases s with
  | none => rfl
  | some s => simp [unit, ifaceSrc]

def group (dl : Dialect) (G : Finset String) (src : String → Option Scala.Src) (I : String → Iface) :
    String → Out :=
  fun u => (unit dl (src u)).run (answer fun v => if v ∈ G then ifaceSrc (src v) else I v)

/-- Lowering, with the `searched` bridge: a key per traced query, hashed by the declaration it read. -/
def compiler (dl : Dialect) :
    IncComp.XCompiler String (Option Scala.Src) Out Iface Bool (Option Decl) Bool (fun _ => Option View) where
  unit := unit dl
  group := group dl
  iface := Out.iface
  answer := answer
  π I u k := side I (u, k)
  hashDeps _ u := {u}
  keys _ _ tr := tr.toFinset
  covers _ q k := q = k

theorem searched_obligations (dl : Dialect) : (compiler dl).Obligations where
  comp G src I u _ := by
    show (unit dl (src u)).run (answer _) = (unit dl (src u)).run (answer _)
    congr 2
    funext v
    simp only [IncComp.XCompiler.override, compiler, Function.comp, group, iface_unit]
  coverage I _ s q hq := ⟨q, List.mem_toFinset.2 hq, rfl⟩
  abstraction I I' k h q hc := by
    subst hc
    refine ⟨?_, rfl⟩
    show (side I q).map _ = (side I' q).map _
    have : side I q = side I' q := h
    rw [this]
  locality I I' c h k := by
    show side I (c, k) = side I' (c, k)
    simp only [side, h c (Finset.mem_singleton_self c)]

/-- The interface is the declaration: source-determined. -/
theorem explicit (dl : Dialect) (sr : Option Scala.Src) (I : String → Iface) :
    (compiler dl).iface (((compiler dl).unit sr).run ((compiler dl).answer I)) = ifaceSrc sr :=
  iface_unit dl sr _

/-! ## Linking -/

/-- The classfiles of the units `us`, as a JVM class table. -/
def worldOf (us : List String) (o : String → Out) : Jvm.World String String String :=
  toWorld ((us.filterMap fun u => (o u).classes.toOption).flatten)

/-- The class table after a library edit with `c` not recompiled: `c`'s old classfiles, everything
else from the new build. -/
def afterWorld (us : List String) (clean : String → Out) (c : String) (old : Out) :
    Jvm.World String String String :=
  worldOf us fun u => if u = c then old else clean u

/-- **Track B4 for lowering.** Under the `searched` bridge (or any bridge meeting the obligations, by
`IncComp.XCompiler.untouched_eq_clean`), a client `c` that Zinc's loop never recompiled links against
the new library exactly as a fresh build does. -/
theorem after_eq_fresh (dl : Dialect) (us : List String) (S : Finset String)
    (src : String → Option Scala.Src) (P : IncComp.Compiler.Policy String Out Bool) (hP : P.Sound S)
    (hPS : P.InS S) (fuel : ℕ) (R₀ D : Finset String) (s : IncComp.Compiler.State String Out Bool)
    (hD : D ⊆ R₀) (hR₀ : R₀ ⊆ S) (hInv : (compiler dl).Inv S src s D)
    (s' : IncComp.Compiler.State String Out Bool) (h : (compiler dl).zinc S src P fuel 0 R₀ s = some s')
    (c : String) (hc : c ∉ (compiler dl).recompiled S src P fuel 0 R₀ s)
    (p : Jvm.Program String String String) :
    Jvm.outcome (afterWorld us ((compiler dl).cleanFrom S src s) c (s.out c)) p =
      Jvm.outcome (worldOf us ((compiler dl).cleanFrom S src s)) p := by
  have := (compiler dl).untouched_eq_clean (searched_obligations dl) ifaceSrc (explicit dl)
    S src P hP hPS fuel R₀ D s hD hR₀ hInv s' h c hc
  unfold afterWorld
  congr 2
  funext u
  split
  · subst_vars; exact this
  · rfl

/-- **Compatible, from Zinc-clean.** If the fresh build links, the old client classfiles link
against the new library. -/
theorem compatible_of_untouched (dl : Dialect) (us : List String) (S : Finset String)
    (src : String → Option Scala.Src) (P : IncComp.Compiler.Policy String Out Bool) (hP : P.Sound S)
    (hPS : P.InS S) (fuel : ℕ) (R₀ D : Finset String) (s : IncComp.Compiler.State String Out Bool)
    (hD : D ⊆ R₀) (hR₀ : R₀ ⊆ S) (hInv : (compiler dl).Inv S src s D)
    (s' : IncComp.Compiler.State String Out Bool) (h : (compiler dl).zinc S src P fuel 0 R₀ s = some s')
    (c : String) (hc : c ∉ (compiler dl).recompiled S src P fuel 0 R₀ s)
    (p : Jvm.Program String String String) (w₀ : Jvm.World String String String)
    (hfresh : (Jvm.outcome (worldOf us ((compiler dl).cleanFrom S src s)) p).toBool = true) :
    Jvm.Compatible w₀ (afterWorld us ((compiler dl).cleanFrom S src s) c (s.out c)) p := by
  intro _
  rw [after_eq_fresh dl us S src P hP hPS fuel R₀ D s hD hR₀ hInv s' h c hc p]
  exact hfresh

/-! ## The converse fails -/

/-- `T` gains a concrete `b`; `X extends T`. -/
def t0 : Scala.Src := Catalogue.trt "T" [Catalogue.dfn "a"]
def t1 : Scala.Src := Catalogue.trt "T" [Catalogue.dfn "a", Catalogue.dfn "b"]
def x : Scala.Src := Catalogue.cls "X" [] none [("T", [])]

def src0 : String → Option Scala.Src := fun u => if u = "T" then some t0 else if u = "X" then some x else none
def src1 : String → Option Scala.Src := fun u => if u = "T" then some t1 else if u = "X" then some x else none

def S : Finset String := {"T", "X"}

/-- The old build: everything compiled against the old sources. -/
def old : String → Out := group .s213 S src0 (fun _ => none)
/-- The fresh build of the new sources. -/
def fresh : String → Out := group .s213 S src1 (fun _ => none)

/-- **The gap.** Adding a concrete method to a trait leaves the old `X` linking against the new `T`
(binary compatible: `X` selects the trait's default `b`), yet `X`'s classfile changes: the fresh
build adds a mixin forwarder. So no sound bridge leaves `X` alone (`must_recompile`), and MiMa,
which compares only the library, reports nothing. -/
theorem gap_witness :
    old "X" ≠ fresh "X" ∧
    Jvm.Compatible (worldOf ["T", "X"] old)
      (worldOf ["T", "X"] fun u => if u = "X" then old "X" else fresh u)
      Catalogue.concreteAddedToTrait.prog := by
  refine ⟨by decide +kernel, ?_⟩
  intro _
  decide +kernel

end Links.ZincBridge
