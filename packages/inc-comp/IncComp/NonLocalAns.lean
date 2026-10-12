import IncComp.Soundness
import IncComp.General
import Mathlib.Data.Fintype.Basic
/-!
# Non-local answers and interface-dependent read sets

`GCompiler` (`NonLocal.lean`) lets a hash read several interfaces, but every *answer* still reads
one: `answer : Iface → Q → A`. That is enough for a Merkle hash that is the verifying trace of a
walk, but not for a hash that summarises the walk's *result*. The Zinc PoC's flattened Merkle hash
is of the second kind: it hashes, per name, the ancestors in the stored linearization that declare
it, so it cannot cover the individual `parents` queries of the walk. The client's member lookup
has to be a single query whose answer reads the receiver's stored linearization and its
ancestors' declarations.

`NCompiler` generalises `GCompiler` in three ways:

* `answer : (CUnit → Iface) → CUnit × Q → A`: an answer may read several interfaces;
* `hashDeps : (CUnit → Iface) → CUnit → Finset CUnit`: the read set of `π _ c _` may depend on the
  interfaces (the stored linearization of `c`);
* `keys : CUnit → …`: the extractor knows which unit it extracts for, so a model can drop
  self-references as Zinc does.

Joint compilation takes the *interfaces* of everything outside the group, since an answer about a
group-mate may read an outsider.

**T2″** (`round_preserves`) is T2′ with `Δ` over `affected R s = R ∪ {c | hashDeps(c) ∩ R ≠ ∅}`,
read sets taken in the state before the round. **T3a″** (`zinc_sound`) follows for any sound policy.
-/

open Query

namespace IncComp

structure NCompiler (CUnit Src Out Iface K Hash Q : Type) (A : Q → Type) where
  unit   : Src → Query.Task (CUnit × Q) (fun p => A p.2) Out
  /-- Joint compilation of a group against the interfaces of everything else. -/
  group  : Finset CUnit → (CUnit → Src) → (CUnit → Iface) → (CUnit → Out)
  iface  : Out → Iface
  /-- An answer may read the interfaces of several units. -/
  answer : (CUnit → Iface) → (q : CUnit × Q) → A q.2
  π      : (CUnit → Iface) → CUnit → K → Hash
  /-- The units `π I c _` reads, which may depend on `I`. -/
  hashDeps : (CUnit → Iface) → CUnit → Finset CUnit
  /-- `U(d)`: the extractor for unit `d`. -/
  keys   : CUnit → List (CUnit × Q) → Finset (CUnit × K)
  covers : (CUnit → Iface) → (CUnit × Q) → (CUnit × K) → Prop

namespace NCompiler

variable {CUnit Src Out Iface K Hash Q : Type} {A : Q → Type}
variable (C : NCompiler CUnit Src Out Iface K Hash Q A)
variable [DecidableEq CUnit]

/-- Replace the interfaces of `G`. -/
def override (I : CUnit → Iface) (G : Finset CUnit) (I' : CUnit → Iface) : CUnit → Iface :=
  fun u => if u ∈ G then I' u else I u

structure Obligations : Prop where
  comp : ∀ (G : Finset CUnit) (src : CUnit → Src) (I : CUnit → Iface), ∀ d ∈ G,
    C.group G src I d = (C.unit (src d)).run (C.answer (override I G (C.iface ∘ C.group G src I)))
  coverage : ∀ (I : CUnit → Iface) (d : CUnit) (s : Src), ∀ q ∈ (C.unit s).trace (C.answer I),
    ∃ k ∈ C.keys d ((C.unit s).trace (C.answer I)), C.covers I q k
  abstraction : ∀ (I I' : CUnit → Iface) (k : CUnit × K), C.π I k.1 k.2 = C.π I' k.1 k.2 →
    ∀ q, C.covers I q k → C.answer I q = C.answer I' q ∧ C.covers I' q k
  locality : ∀ (I I' : CUnit → Iface) (c : CUnit), (∀ d ∈ C.hashDeps I c, I d = I' d) →
    ∀ k, C.π I c k = C.π I' c k

open Compiler (State Policy)

def ifaces (s : State CUnit Out K) : CUnit → Iface := C.iface ∘ s.out

/-- The lift into the general form (`General.lean`): the extractor ignores the output. -/
def toX : XCompiler CUnit Src Out Iface K Hash Q A where
  unit := C.unit
  group := C.group
  iface := C.iface
  answer := C.answer
  π := C.π
  hashDeps := C.hashDeps
  keys u _ tr := C.keys u tr
  covers := C.covers

/-- A round is the general form's, on the lift. -/
def round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) : State CUnit Out K :=
  C.toX.round src R s

/-- A round's outputs: the group's for the units in the round, the old ones elsewhere. -/
theorem round_out (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) (u : CUnit) :
    (C.round src R s).out u = if u ∈ R then C.group R src (C.ifaces s) u else s.out u := rfl

variable [Fintype CUnit]

/-- The units whose hash may have changed after recompiling `R`, read sets taken in `s`. -/
def affected (R : Finset CUnit) (s : State CUnit Out K) : Finset CUnit :=
  R ∪ Finset.univ.filter fun c => ∃ d ∈ C.hashDeps (C.ifaces s) c, d ∈ R

def changed (Dom : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) : Prop :=
  p.1 ∈ Dom ∧ C.π (C.ifaces s) p.1 p.2 ≠ C.π (C.ifaces s') p.1 p.2

instance [DecidableEq Hash] (Dom : Finset CUnit) (s s' : State CUnit Out K) (p : CUnit × K) :
    Decidable (C.changed Dom s s' p) := by unfold changed; infer_instance

def invalidated [DecidableEq K] [DecidableEq Hash] (S Dom : Finset CUnit)
    (s s' : State CUnit Out K) : Finset CUnit :=
  S.filter fun d => ∃ p ∈ s'.U d, C.changed Dom s s' p

def UpToDate (src : CUnit → Src) (s : State CUnit Out K) (u : CUnit) : Prop :=
  s.out u = (C.unit (src u)).run (C.answer (C.ifaces s)) ∧
  ∀ q ∈ (C.unit (src u)).trace (C.answer (C.ifaces s)), ∃ k ∈ s.U u, C.covers (C.ifaces s) q k

def Inv (S : Finset CUnit) (src : CUnit → Src) (s : State CUnit Out K) (D : Finset CUnit) : Prop :=
  ∀ u ∈ S, u ∉ D → C.UpToDate src s u

omit [Fintype CUnit] in
theorem ifaces_round (src : CUnit → Src) (R : Finset CUnit) (s : State CUnit Out K) :
    C.ifaces (C.round src R s) = override (C.ifaces s) R (C.iface ∘ C.group R src (C.ifaces s)) := by
  funext u
  simp only [ifaces, round, XCompiler.round, XCompiler.ifaces, toX, override, Function.comp]
  split <;> rfl

variable [DecidableEq K] [DecidableEq Hash]

omit [Fintype CUnit] [DecidableEq K] [DecidableEq Hash] in
theorem toX_obligations (ob : C.Obligations) : C.toX.Obligations :=
  ⟨ob.comp, ob.coverage, ob.abstraction, ob.locality⟩

/-- The lift's `inv(ΔAPI)` is this one: its affected units are `affected`. -/
theorem invalidated_toX (S R : Finset CUnit) (s s' : State CUnit Out K) :
    C.toX.invalidated S R s s' = C.invalidated S (C.affected R s) s s' := by
  unfold XCompiler.invalidated invalidated
  apply Finset.filter_congr
  intro d _
  simp only [XCompiler.changed, changed, XCompiler.Affected, affected, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- **T2″.** With `Δ` over `affected R s`, one round preserves the invariant
(`XCompiler.round_preserves` on the lift). -/
theorem round_preserves (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (s : State CUnit Out K) (D R : Finset CUnit) (hD : D ⊆ R) (hInv : C.Inv S src s D) :
    C.Inv S src (C.round src R s)
      (C.invalidated S (C.affected R s) s (C.round src R s) \ R) := by
  have := C.toX.round_preserves (C.toX_obligations ob) S src s D R hD hInv
  rwa [invalidated_toX] at this

/-- Zinc's loop with `Δ` over `affected`: the general form's loop, on the lift (`invalidated_toX`
says its `inv(ΔAPI)` is this compiler's over `affected`). -/
def zinc (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ℕ → ℕ → Finset CUnit → State CUnit Out K → Option (State CUnit Out K) :=
  C.toX.zinc S src P

/-- The loop on the lift is this loop. -/
theorem zinc_toX (S : Finset CUnit) (src : CUnit → Src) (P : Policy CUnit Out K) :
    ∀ fuel n R s, C.toX.zinc S src P fuel n R s = C.zinc S src P fuel n R s :=
  fun _ _ _ _ => rfl

/-- **T3a″.** If the loop stops, no unit is dirty (`XCompiler.zinc_sound` on the lift). -/
theorem zinc_sound (ob : C.Obligations) (S : Finset CUnit) (src : CUnit → Src)
    (P : Policy CUnit Out K) (hP : P.Sound S) :
    ∀ (fuel n : ℕ) (R : Finset CUnit) (s : State CUnit Out K) (D : Finset CUnit),
      D ⊆ R → C.Inv S src s D →
      ∀ s', C.zinc S src P fuel n R s = some s' → C.Inv S src s' ∅ := by
  intro fuel n R s D hD hInv s' h
  rw [← zinc_toX] at h
  exact C.toX.zinc_sound (C.toX_obligations ob) S src P hP fuel n R s D hD hInv s' h

end NCompiler
end IncComp
