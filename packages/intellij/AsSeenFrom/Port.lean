import AsSeenFrom.Scalac
import AsSeenFrom.Shared

/-!
# This model as an instance of the shared `asSeenFrom`

`Shared.lean` (vendored from retronym/talks) states scalac's walk once, for any type language
with substitutable leaves, and proves the composition law there. This file makes `Ty` such a
language (its leaves are this-types; it has no class type parameters, so `bargs` is empty) and
proves that `Scalac.asf` *is* the shared map. `Chain.compose` and `Chain.chain_is_single` are then
the shared theorems (`compose_of_shared`, `chain_is_single_of_shared`).
-/

namespace Port

open AsSeenFrom

/-- A leaf of `Ty` is a this-type, named by its class. -/
instance : Leafy Class Nat where
  cls d := d
  kind _ := .this

def Ty.bind : Ty → (Class → Ty) → Ty
  | .this d,   f => f d
  | .sel q v,  f => .sel (Ty.bind q f) v
  | .pair a b, f => .pair (Ty.bind a f) (Ty.bind b f)
  | .tvar n,   _ => .tvar n

instance : Subst Ty Class where
  leaf := .this
  bind := Ty.bind
  leaves := Ty.thisLeaves

theorem Ty.bind_bind (t : Ty) (f g : Class → Ty) :
    Ty.bind (Ty.bind t f) g = Ty.bind t (fun l => Ty.bind (f l) g) := by
  induction t with
  | this d => rfl
  | sel q v ih => simp only [Ty.bind, ih]
  | pair a b iha ihb => simp only [Ty.bind, iha, ihb]
  | tvar n => rfl

theorem Ty.bind_congr (t : Ty) (f g : Class → Ty) (h : ∀ l ∈ t.thisLeaves, f l = g l) :
    Ty.bind t f = Ty.bind t g := by
  induction t with
  | this d => exact h d (by simp [Ty.thisLeaves])
  | sel q v ih => simp only [Ty.bind, ih (fun d hd => h d (by simpa [Ty.thisLeaves] using hd))]
  | pair a b iha ihb =>
    simp only [Ty.bind, iha (fun d hd => h d (by simp [Ty.thisLeaves, hd])),
      ihb (fun d hd => h d (by simp [Ty.thisLeaves, hd]))]
  | tvar n => rfl

instance : LawfulSubst Ty Class where
  bind_leaf _ _ := rfl
  bind_bind := Ty.bind_bind
  bind_congr := Ty.bind_congr

/-- The world, with no class type parameters. -/
def _root_.World.shared (W : World) : AsSeenFrom.World Nat Ty := { bpre := W.bpre, hasBase := W.hasBase }

variable (W : World)

theorem thisAsSeen_eq (d c : Class) (p : Ty) :
    Scalac.thisAsSeen W d c p = leafAsSeen W.shared d c p := by
  induction c generalizing p with
  | nil => rfl
  | cons x rest ih =>
    have e : hit W.shared d (x :: rest) p = (decide (x :: rest = d) && W.hasBase p (x :: rest)) := rfl
    simp only [Scalac.thisAsSeen, leafAsSeen, e]
    by_cases hc : (decide (x :: rest = d) && W.hasBase p (x :: rest)) = true
    · simp only [hc, ↓reduceIte]; rfl
    · simp only [hc]; exact ih _

theorem rewrites_eq (d c : Class) (p : Ty) :
    Scalac.rewrites W d c p = AsSeenFrom.rewrites W.shared d c p := by
  induction c generalizing p with
  | nil => rfl
  | cons x rest ih =>
    have e : hit W.shared d (x :: rest) p = (decide (x :: rest = d) && W.hasBase p (x :: rest)) := rfl
    simp only [Scalac.rewrites, AsSeenFrom.rewrites, e]
    by_cases hc : (decide (x :: rest = d) && W.hasBase p (x :: rest)) = true
    · simp only [hc, ↓reduceIte]; rfl
    · simp only [hc]; exact ih _

/-- **`Scalac.asf` is the shared map.** -/
theorem asf_eq (p : Ty) (c : Class) (t : Ty) : Scalac.asf W p c t = AsSeenFrom.asf W.shared p c t := by
  induction t with
  | this d => exact thisAsSeen_eq W d c p
  | sel q v ih => simp only [Scalac.asf, ih]; rfl
  | pair a b iha ihb => simp only [Scalac.asf, iha, ihb]; rfl
  | tvar n => rfl

theorem inView_iff (p : Ty) (c : Class) (t : Ty) :
    Scalac.inView W p c t ↔ AsSeenFrom.inView W.shared p c t := by
  simp only [Scalac.inView, AsSeenFrom.inView, rewrites_eq]; rfl

/-- This model's lockstep is the shared one (with no type arguments to commute). -/
theorem lockstep (hb : ∀ p₂ c₂ p c, Scalac.asf W p₂ c₂ (W.bpre p c) = W.bpre (Scalac.asf W p₂ c₂ p) c)
    (hh : ∀ p₂ c₂ p c, W.hasBase (Scalac.asf W p₂ c₂ p) c = W.hasBase p c) :
    AsSeenFrom.Lockstep W.shared where
  bpre_comm p₂ c₂ p c := by simpa [asf_eq, World.shared] using hb p₂ c₂ p c
  hasBase_comm p₂ c₂ p c := by simpa [asf_eq, World.shared] using hh p₂ c₂ p c
  bargs_comm _ _ _ _ := rfl

end Port
