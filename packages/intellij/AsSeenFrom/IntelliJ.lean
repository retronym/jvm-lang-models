import AsSeenFrom.Scalac

/-!
# IntelliJ's walk: scalac's, plus a fallback

`ThisTypeSubstitution.doUpdateThisTypeFromClass` is scalac's walk with one departure
that matters here: when `baseType target cursor` does not exist, instead of stepping to
an empty prefix (and so leaving the this-type alone, as scalac does once the prefix is
exhausted), it *narrows against the target directly*, gated by owner-chain matching:
rewrite `D.this` to `target` if the cursor's owner chain reaches `D` (same class or an
inheritor) and `target`'s class inherits `D`.

The other departures (the anchorless mode, the `toPrefix` early exit, the self-type
allowance) are shortcuts of the same kind and are not modelled separately; the point
is to show that a single such fallback already makes the walk disagree with scalac on
a concrete prefix, and to prove it agrees whenever the fallback does not fire.
-/

namespace IntelliJ
open Scalac

/-- What the fallback needs from the environment beyond `World`. -/
structure Env extends World where
  /-- `isInheritorDeep a b`: class `a` is `b` or inherits from `b`. -/
  inherits : Class → Class → Bool
  /-- The class a prefix denotes once widened (`target.widen.extractClass`). -/
  clsOf : Ty → Class

variable (E : Env)

/-- Environment facts the fallback relies on: a class inherits itself, and a prefix whose
base types include `d` has a widened class that inherits `d`. -/
class Coherent : Prop where
  inherits_refl   : ∀ c, E.inherits c c = true
  hasBase_inherits : ∀ p d, E.hasBase p d = true → E.inherits (E.clsOf p) d = true

/-- `ownerChainReaches`: some class on the cursor's owner chain is `d` or inherits it. -/
def reaches (d : Class) : Class → Bool
  | []             => false
  | c@(_ :: rest)  => E.inherits c d || reaches d rest

/-- `doUpdateThisType` with the prefix climb elided: narrow if the target inherits `d`. -/
def narrow (d : Class) (p : Ty) : Ty :=
  if E.inherits (E.clsOf p) d then p else .this d

def thisAsSeen (d : Class) : Class → Ty → Ty
  | [],            _ => .this d
  | c@(_ :: rest), p =>
      if c = d then (if reaches E d c then narrow E d p else .this d)
      else if E.hasBase p c then thisAsSeen d rest (E.bpre p c)
      else if reaches E d c then narrow E d p else .this d

/-- The walk never consults the fallback along `c` over `p`: at every step either the
cursor matches with a base type present, or a base type is present to step through. -/
def faithfulOn (d : Class) : Class → Ty → Prop
  | [],            _ => True
  | c@(_ :: rest), p =>
      E.hasBase p c = true ∧ (c = d ∨ faithfulOn d rest (E.bpre p c))

/-- Where the fallback does not fire, IntelliJ's walk is scalac's. -/
theorem agrees [Coherent E] (d c : Class) (p : Ty) (hf : faithfulOn E d c p) :
    thisAsSeen E d c p = Scalac.thisAsSeen E.toWorld d c p := by
  induction c generalizing p with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨hb, hcase⟩ := hf
    simp only [thisAsSeen, Scalac.thisAsSeen]
    by_cases hc : x :: rest = d
    · subst hc
      -- cursor matches and hasBase holds: scalac returns p; IntelliJ narrows p against
      -- its own class, which is the identity when the target's class is itself (the
      -- `targetDenotesLeafClass` admission); we need that `narrow` returns p here.
      have hr : reaches E (x :: rest) (x :: rest) = true := by
        simp [reaches, Coherent.inherits_refl]
      simp only [hb, ↓reduceIte, decide_true, Bool.true_and, hr, narrow,
                 Coherent.hasBase_inherits _ _ hb]
    · simp only [hc, ↓reduceIte, decide_false, Bool.false_and, hb]
      rcases hcase with h | h
      · exact absurd h hc
      · exact ih _ h

end IntelliJ
