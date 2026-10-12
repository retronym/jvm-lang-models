import VersoManual
import ScalaTypes.Members

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Overriding in Scala" =>
%%%
shortTitle := "Scala overriding"
htmlSplit := .never
%%%

Scala's overriding rules are checked by the compiler's refchecks phase, one overriding pair at a
time. The specification states them as restrictions on the overriding and the overridden member:

> A member M of class C that matches a non-private member M' of a base class of C is said to override that member. In this case the binding of the overriding member M must subsume the binding of the overridden member M'. Furthermore, the following restrictions on modifiers apply to M and M':

— [SLS §5.1.4](https://scala-lang.org/files/archive/spec/2.13/05-classes-and-objects.html#overriding), Scala 2.13.

Two of the restrictions concern values:

> * If M and M' are both concrete value definitions, then either none of them is marked lazy or both must be marked lazy.
  * A stable member can only be overridden by a stable member.

— [SLS §5.1.4](https://scala-lang.org/files/archive/spec/2.13/05-classes-and-objects.html#overriding), Scala 2.13.

The model computes the errors scalac and dotc report for a program, and for a program that
compiles, which `m` a call runs. Calibrated over 4,704 programs, it agrees with dotc 3.9.0 on all of
them and with scalac 2.12.21 and 2.13.18 on all but four:

{docstring Scala.Members.errors}

# A stable member redeclared as a method

The four programs share one shape:

```
trait T { val m = "T" }
abstract class B extends T { def m: String }
class C extends B with T { override val m = "C" }
```

Does `B`'s `def m` override the stable `T.m`, against the second rule? The section before says it
does not:

> This definition also determines the overriding relationships between matching members of a class C and its parents. First, a concrete definition always overrides an abstract definition.

— [SLS §5.1.3](https://scala-lang.org/files/archive/spec/2.13/05-classes-and-objects.html#class-members), Scala 2.13.

Read literally, `B`'s `def m` declares nothing: `B`'s member is `T`'s `val`, and the program is
legal. The specification has no notion of a class re-abstracting an inherited concrete member, but
both compilers have one, in different forms.
dotc forms an overriding pair of `B.m` and `T.m` and rejects `B` by the stability rule.
scalac forms no pair, so it checks nothing about `B.m`, but it does oblige every concrete subclass
of `B` to implement `m`. The model has the same split:

```lean
open Scala Scala.Members

/-- `T`, `B` and `C` above. -/
def shape : Program :=
  program .val .none false .abs true .ovrVal
```

```lean (name := s2)
#eval errors .s213 shape
```
```leanOutput s2
Except.ok []
```

```lean (name := s3)
#eval errors .s3 shape
```
```leanOutput s3
Except.ok [{ cls := "B", kind := Scala.Members.Kind.stable }]
```

```lean
example : errors .s213 shape = .ok [] ∧
    errors .s3 shape =
      .ok [{ cls := "B", kind := .stable }] := by
  decide +kernel
```

The model predicts that `C`'s `m` runs, and scalac 2.12 and 2.13 compile the program, but `new C`
throws `AbstractMethodError`.
A trait's `val` is a field of the class that mixes the trait in, and the trait's initializer
`T.$init$` stores into it through a setter, `T$_setter_$m_$eq`, that the class implements.
scalac's Fields phase sees that `B` redeclares `m`, gives `B` no field, and drops the setter, so
no class implements it.
Reported as [scala/bug#13199](https://github.com/scala/bug/issues/13199). The draft fix in
[retronym/scala#136](https://github.com/retronym/scala/pull/136) keeps the setter with an empty
body, and under `-Xsource:3` reports what dotc rejects.
