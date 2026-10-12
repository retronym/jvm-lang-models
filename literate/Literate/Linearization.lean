import VersoManual
import ScalaTypes.Members

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Linearization" =>
%%%
shortTitle := "Linearization"
htmlSplit := .never
%%%

A Scala class can mix in several traits, so its base classes form a graph rather than a chain.
Which member a call runs, and which member overrides which, is decided along one order of that
graph:

> The classes reachable through transitive closure of the direct inheritance relation from a class C are called the base classes of C. Because of mixins, the inheritance relationship on base classes forms in general a directed acyclic graph. A linearization of this graph is defined as follows.

— [SLS §5.1.2](https://scala-lang.org/files/archive/spec/2.13/05-classes-and-objects.html#class-linearization), Scala 2.13.

The definition that follows is a formula. For a class `C` with template
`C1 with … with Cn { stats }`, `L(C)` is `C` followed by the concatenation of `L(Cn)`, …, `L(C1)`,
where an element of a left operand is dropped if it also occurs in the right one. The model computes
it for a class whose parents may take type arguments:

{docstring Scala.lin}

# The specification's example

```lean
open Scala Scala.Members

def cls (n : String) (ps : List String)
    (k : Scala.Kind := .cls) : Src :=
  decl n k ps []

def iters : Program :=
  [cls "AbsIterator" [],
   cls "RichIterator" ["AbsIterator"] .trt,
   cls "StringIterator" ["AbsIterator"],
   cls "Iter" ["StringIterator", "RichIterator"]]

/-- The linearization of `n` in `p`, by name. -/
def linOf (p : Program) (n : String) :
    Except String (List String) :=
  match p.find? (·.name = n) |>.bind (·.cls) with
  | none => .error s!"no class {n}"
  | some d =>
    ((lin fuel d).run.run p.env).map
      (·.map (·.1.name))
```

```lean (name := iterEval)
#eval linOf iters "Iter"
```
```leanOutput iterEval
Except.ok ["Iter", "RichIterator", "StringIterator", "AbsIterator"]
```

The specification gives `{ Iter, RichIterator, StringIterator, AbsIterator, AnyRef, Any }`; the
model's programs have no `AnyRef` or `Any`. It then states two properties:

> Note that the linearization of a class refines the inheritance relation: if C is a subclass of D, then C precedes D in any linearization where both C and D occur. Linearization also satisfies the property that a linearization of a class always contains the linearization of its direct superclass as a suffix.

— [SLS §5.1.2](https://scala-lang.org/files/archive/spec/2.13/05-classes-and-objects.html#class-linearization), Scala 2.13.

On the example, `StringIterator`'s linearization is a suffix of `Iter`'s and `RichIterator`'s is
not, as the specification goes on to say:

```lean
example :
    (do
      let i ← linOf iters "Iter"
      let s ← linOf iters "StringIterator"
      let r ← linOf iters "RichIterator"
      pure (s.isSuffixOf i, r.isSuffixOf i)) =
    Except.ok (true, false) := by
  decide +kernel
```

# Which member runs

A call runs the first concrete member along the linearization. Mixing in a trait that is already a
base class of a later one does not move it:

```lean
def stack (ts : List String) : Program :=
  [decl "T" .trt [] [mem .str false],
   decl "U" .trt ["T"] [mem .str false],
   decl "B" .cls [] [],
   decl "C" .cls ("B" :: ts) []]
```

```lean (name := stackEval)
#eval (runs (stack ["T", "U"]),
       runs (stack ["U", "T"]))
```
```leanOutput stackEval
([("C", "U")], [("C", "U")])
```

In `C extends B with U with T`, `L(T)` comes first, and `L(U)`, to its right, contains `T`, so the
first `T` is dropped: the order is `C, U, T, B` either way.
The overriding checks of the Scala overriding page walk the same order, pair by pair.
