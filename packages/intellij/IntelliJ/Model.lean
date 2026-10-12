/-!
# Model: classes, types, prefixes

The model keeps just enough of Scala's types to state what an `asSeenFrom` walk does.

A **class** is its path from the root of the owner tree, innermost first:
`[c, owner c, owner (owner c), …]`. So `List.tail` is `owner`, the empty list stands for
the package, and the classes enclosing `c` are the suffixes of its list. This turns
scalac's climb through the enclosing classes into structural recursion on a list.

A **type** is a tree whose interesting leaves are this-types: `.this d` is `D.this`.
A path `q.v` and a type projection `q#n` both map their prefix `q` and leave the name
alone, so one constructor `sel` models both. `pair` stands for any other structure
(type arguments, compounds), enough to show that a map goes through structure without
rewriting it. `tvar` is a type parameter, the leaf a type-argument binding rewrites.
A **prefix** is a type, as in scalac.

A **world** supplies the only two facts scalac's walk reads off the environment:
`bpre p c` is `(p baseType c).prefix`, the instance enclosing `c` as `p` sees it, and
`hasBase p c` says that `c` is a base class of `p` (`p.baseTypeIndex(c) != -1`).
**Nothing else about base types is assumed, so every theorem holds for any class table
that supplies these two facts.**
-/

abbrev Class := List Nat

inductive Ty where
  | this : Class → Ty
  | sel  : Ty → Nat → Ty
  | pair : Ty → Ty → Ty
  | tvar : Nat → Ty
  deriving DecidableEq, Repr

structure World where
  bpre    : Ty → Class → Ty
  hasBase : Ty → Class → Bool

/-- Every this-type in a type, in order. -/
def Ty.thisLeaves : Ty → List Class
  | .this d   => [d]
  | .sel q _  => q.thisLeaves
  | .pair a b => a.thisLeaves ++ b.thisLeaves
  | .tvar _   => []
