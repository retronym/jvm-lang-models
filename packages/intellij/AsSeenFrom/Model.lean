/-!
# Model: classes, types, prefixes

A **class** is its path from the root of the owner tree, innermost first:
`[c, owner c, owner (owner c), …]`. So `List.tail` is `owner`, the empty list is
the package, and the owner chain of a class is the list of its suffixes. This makes
scalac's owner-chain walk a structural recursion.

A **type** is a tree whose leaves of interest are this-types. Paths (`q.v`) and type
projections (`q#n`) both map their prefix and are modelled by one constructor; any
other structure is modelled by `pair`, which is enough to show that maps go through
structure without rewriting it. A prefix is a type (as in scalac).

A **world** supplies the two facts scalac's walk reads off the environment:
`bpre p c` is `(p baseType c).prefix`, the enclosing instance of `c` as `p` sees it,
and `hasBase p c` is `p.baseTypeIndex(c) != -1`. Nothing else about base types is
assumed.
-/

abbrev Class := List Nat

inductive Ty where
  | this : Class → Ty
  | sel  : Ty → Nat → Ty
  | pair : Ty → Ty → Ty
  | tvar : Nat → Ty          -- a type parameter / type variable, for `TypeParamSubstitution`
  deriving DecidableEq, Repr

structure World where
  bpre    : Ty → Class → Ty
  hasBase : Ty → Class → Bool

/-- Every this-leaf of a type, in order. -/
def Ty.thisLeaves : Ty → List Class
  | .this d   => [d]
  | .sel q _  => q.thisLeaves
  | .pair a b => a.thisLeaves ++ b.thisLeaves
  | .tvar _   => []
