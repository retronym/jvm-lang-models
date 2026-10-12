import IncComp.Soundness
import IncComp.General
/-!
# Keys from the typed tree

`Compiler.keys` maps a unit's *trace* to the keys Zinc records: an idealised extractor that sees
every query the compilation asked. Zinc's extractors (`ExtractUsedNames`, `ExtractDependencies`)
read the *typed tree* instead, at a fixed point in the pipeline. Two kinds of query never reach it:

* lookups the typer made and then discarded: a failed lookup of `+=` before desugaring `x += y`
  to `x = x + y`, `selectDynamic` for `Dynamic`;
* lookups made by phases after extraction: the pattern matcher's `_1`, `_2` and arity checks,
  erasure, mixin.

`TCompiler` is `Compiler` with `keysOf : Out → Finset Key`, a function of the output (which
contains the typed tree). The obligations and the loop are unchanged otherwise; coverage now
relates the trace to what the tree shows. T2 and T3a carry over with the same proofs
(`round_preserves`, `zinc_sound`). `TreeToy.lean` has the counterexamples and the fixes:
recording failed lookups, and anticipatory keys for the names a later phase will ask.
-/

namespace Zinc

structure TCompiler (CUnit Src Out Iface K Hash Q : Type) (A : Q → Type) where
  unit   : Src → Task (CUnit × Q) (fun p => A p.2) Out
  group  : Finset CUnit → (CUnit → Src) → Task.Env (CUnit × Q) (fun p => A p.2) → (CUnit → Out)
  iface  : Out → Iface
  answer : Iface → (q : Q) → A q
  π      : Iface → K → Hash
  /-- `U(d)`, extracted from the output (the typed tree), not from the trace. -/
  keysOf : Out → Finset (CUnit × K)
  covers : Q → K → Prop

namespace TCompiler

open Compiler (State Policy)

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : TCompiler CUnit Src Out Iface K Hash Q A)

abbrev Env := Task.Env (CUnit × Q) (fun p => A p.2)

def envOf (I : CUnit → Iface) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  fun p => C.answer (I p.1) p.2

variable [DecidableEq CUnit]

def override (e : Env (CUnit := CUnit) (Q := Q) (A := A)) (G : Finset CUnit)
    (I : CUnit → Iface) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  fun p => if p.1 ∈ G then C.answer (I p.1) p.2 else e p

theorem override_envOf (I I' : CUnit → Iface) (G : Finset CUnit) :
    C.override (C.envOf I) G I' = C.envOf (fun u => if u ∈ G then I' u else I u) := by
  funext p
  simp only [override, envOf]
  split <;> rfl

structure Obligations : Prop where
  comp : ∀ (G : Finset CUnit) (src : CUnit → Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
    ∀ d ∈ G, C.group G src e d =
      (C.unit (src d)).run (C.override e G (C.iface ∘ C.group G src e))
  /-- Every traced query has a key among those the tree yields. -/
  coverage : ∀ (s : Src) (e : Env (CUnit := CUnit) (Q := Q) (A := A)),
    ∀ q ∈ (C.unit s).trace e, ∃ k ∈ C.keysOf ((C.unit s).run e), q.1 = k.1 ∧ C.covers q.2 k.2
  abstraction : ∀ (i i' : Iface) (k : K), C.π i k = C.π i' k →
    ∀ q, C.covers q k → C.answer i q = C.answer i' q

def env (s : State CUnit Out K) : Env (CUnit := CUnit) (Q := Q) (A := A) :=
  C.envOf (C.iface ∘ s.out)

/-- The lift into the general form (`General.lean`): answers and hashes read one interface, keys
come from the output. -/
def toX : XCompiler CUnit Src Out Iface K Hash Q A where
  unit := C.unit
  group G src I := C.group G src (C.envOf I)
  iface := C.iface
  answer I q := C.answer (I q.1) q.2
  π I c k := C.π (I c) k
  hashDeps _ c := {c}
  keys _ o _ := C.keysOf o
  covers _ q k := q.1 = k.1 ∧ C.covers q.2 k.2

/-! The loop is the general form's, on the lift: one definition of a round, of what changed and of
the loop, for every variant (`General.lean`). -/

def round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) : State CUnit Out K :=
  C.toX.round src R s

variable [DecidableEq K] [DecidableEq Hash] in
def invalidated (S R : Finset CUnit) (s s' : State CUnit Out K) : Finset CUnit :=
  C.toX.invalidated S R s s'

variable [DecidableEq K] [DecidableEq Hash] in
def zinc (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ℕ → ℕ → Finset CUnit → State CUnit Out K → Option (State CUnit Out K) :=
  C.toX.zinc S src P

def UpToDate (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (C.unit (src u)).run (C.env s) ∧
  ∀ q ∈ (C.unit (src u)).trace (C.env s), ∃ k ∈ s.U u, q.1 = k.1 ∧ C.covers q.2 k.2

def Inv (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) : Prop :=
  ∀ u ∈ S, u ∉ D → C.UpToDate src s u

/-- A round's outputs: the group's for the units in the round, the old ones elsewhere. -/
theorem round_out (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) (u : CUnit) :
    (C.round src R s).out u = if u ∈ R then C.group R src (C.env s) u else s.out u := rfl

theorem env_round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) :
    C.env (C.round src R s) = C.override (C.env s) R (C.iface ∘ C.group R src (C.env s)) := by
  simp only [env, round, XCompiler.round, XCompiler.ifaces, toX]
  rw [override_envOf]
  congr 1
  funext u
  simp only [Function.comp]
  split <;> rfl

variable [DecidableEq K] [DecidableEq Hash]

omit [DecidableEq K] [DecidableEq Hash] in
theorem toX_obligations (ob : C.Obligations) : C.toX.Obligations where
  comp G src I d hd := by
    show C.group G src (C.envOf I) d = (C.unit (src d)).run _
    rw [ob.comp G src (C.envOf I) d hd, C.override_envOf]
    rfl
  coverage I _ s q hq := ob.coverage s (C.envOf I) q hq
  abstraction I I' k h q hc := by
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, h1, h2⟩
    show C.answer (I q.1) q.2 = C.answer (I' q.1) q.2
    rw [h1]
    exact ob.abstraction _ _ k.2 h q.2 h2
  locality I I' c h k := by
    show C.π (I c) k = C.π (I' c) k
    rw [h c (Finset.mem_singleton_self c)]

theorem invalidated_toX (S R : Finset CUnit) (s s' : State CUnit Out K) :
    C.toX.invalidated S R s s' = C.invalidated S R s s' := rfl

/-- The loop on the lift is this loop. -/
theorem zinc_toX (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ∀ fuel n R s, C.toX.zinc S src P fuel n R s = C.zinc S src P fuel n R s :=
  fun _ _ _ _ => rfl

/-- **T2, keys from the tree** (`XCompiler.round_preserves` on the lift). -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R) (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s) (C.invalidated S R s (C.round src R s) \ R) := by
  have := C.toX.round_preserves (C.toX_obligations ob) S src s D R hD hInv
  rwa [invalidated_toX] at this

/-- **T3a, keys from the tree** (`XCompiler.zinc_sound` on the lift). -/
theorem zinc_sound (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) (hP : P.Sound S) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K) (D : Finset CUnit),
      D ⊆ R → C.Inv S src s D →
      ∀ s', C.zinc S src P fuel n R s = some s' → C.Inv S src s' ∅ := by
  intro fuel n R s D hD hInv s' h
  rw [← zinc_toX] at h
  exact C.toX.zinc_sound (C.toX_obligations ob) S src P hP fuel n R s D hD hInv s' h

end TCompiler
end Zinc
