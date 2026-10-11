/-!
# Small instances the Mathlib-free layers need

Mathlib provides these; the layers that do not depend on Mathlib (`Jvm`, `Java`, `Scala`) get them
from here.
-/

namespace Query

/-- Decidable equality of `Except`, so that `decide` can check an expected link result. -/
instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error _, .ok _ => isFalse (by intro h; cases h)
  | .ok _, .error _ => isFalse (by intro h; cases h)

/-- `List` as a monad, for enumerating program spaces with `do`. Low priority, so that Mathlib's
instance wins wherever both are in scope. -/
instance (priority := low) instMonadList : Monad List where
  pure a := [a]
  bind l f := l.flatMap f

/-- Remove duplicates, keeping the *last* occurrence of each element, as Mathlib's `List.dedup`
does. Structural, so `decide` can evaluate it. -/
def dedupLast {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then dedupLast l else a :: dedupLast l

end Query
