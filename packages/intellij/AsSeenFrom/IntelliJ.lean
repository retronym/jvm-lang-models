import AsSeenFrom.Scalac

/-!
# The plugin's walk: scalac's, plus a fallback

`ThisTypeSubstitution.doUpdateThisTypeFromClass` follows scalac's walk, with one
departure that matters here. When the target has no base type for the cursor, scalac
steps to an empty prefix and, once the prefix is exhausted, leaves the this-type alone.
The plugin instead *narrows against the target directly*, gated by owner-chain matching:
it rewrites `D.this` to the target if the cursor or an enclosing class is `D` or inherits
it, and the target's class inherits `D`. The fallback exists for paths to inner classes
(`global.AstTransformer`) that are not a base class of the target.

The plugin's other departure, the early exit for a this-type of a proper superclass of
the cursor (scalac's `toPrefix` first branch), is not modelled. The point is that one
fallback already makes the walk disagree with scalac on a concrete prefix (`Cases.A`),
and that the walk agrees with scalac wherever the fallback does not fire (`agrees`).
-/

namespace IntelliJ
open Scalac

/-- What the fallback reads from the environment beyond `World`. -/
structure Env extends World where
  /-- `isInheritorDeep a b`: class `a` is `b` or inherits from `b`. -/
  inherits : Class → Class → Bool
  /-- The class a prefix denotes once widened (`target.widen.extractClass`). -/
  clsOf : Ty → Class

variable (E : Env)

/-- Two facts tying `inherits` and `clsOf` to the world: a class inherits itself, and a
prefix that has `d` as a base class widens to a class that inherits `d`. -/
class Coherent : Prop where
  inherits_refl   : ∀ c, E.inherits c c = true
  hasBase_inherits : ∀ p d, E.hasBase p d = true → E.inherits (E.clsOf p) d = true

/-- `ownerChainReaches`: the cursor or one of its enclosing classes is `d` or inherits it. -/
def reaches (d : Class) : Class → Bool
  | []             => false
  | c@(_ :: rest)  => E.inherits c d || reaches d rest

/-- `doUpdateThisType` with its climb through the target's prefixes elided: rewrite to
the target if the target's class inherits `d`. -/
def narrow (d : Class) (p : Ty) : Ty :=
  if E.inherits (E.clsOf p) d then p else .this d

def thisAsSeen (d : Class) : Class → Ty → Ty
  | [],            _ => .this d
  | c@(_ :: rest), p =>
      if c = d then (if reaches E d c then narrow E d p else .this d)
      else if E.hasBase p c then thisAsSeen d rest (E.bpre p c)
      else if reaches E d c then narrow E d p else .this d

/-- The fallback does not fire on the walk anchored at `c` over `p`: at every step the
prefix has the cursor as a base class, so the walk either matches or steps out. -/
def faithfulOn (d : Class) : Class → Ty → Prop
  | [],            _ => True
  | c@(_ :: rest), p =>
      E.hasBase p c = true ∧ (c = d ∨ faithfulOn d rest (E.bpre p c))

/-- **Where the fallback does not fire, the plugin's walk is scalac's.** So a
disagreement between the two can only come from the fallback, from a wrong anchor, or
from a wrong prefix, and never from the walk itself.

The theorem is about anchored walks: both walks start from a class. The plugin used to
have an anchorless mode as well, `ScSubstitutor(target, null)`, which rewrote any
this-type whose class the target inherits. Its check A6 counted every anchorless link;
almost all were for synthetic members such as `==`, whose types mention no this-type,
and members of refinement types, already handled by the compound type's own link. Both
now get no link at all, and the anchorless mode is deleted. -/
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
