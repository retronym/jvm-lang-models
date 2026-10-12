# Draft: scala/scala3 issue

**Title:** Re-abstraction by a trait is accepted or rejected depending on whether the concrete trait is also a direct parent

## Compiler version

3.9.0

## Minimized code

```scala
trait M { def m: String = "" }
trait A extends M { def m: String }
class B extends A
```

## Output

```
-- [E231] Declaration Error: p3.scala:4:6
  |class B needs to be abstract, since def m: String in trait A is not defined
```

Adding `M` as a direct parent, which changes neither the linearization (`B, A, M`) nor the member that `A` re-declares, makes it compile:

```scala
trait M { def m: String = "" }
trait A extends M { def m: String }
class B extends M with A    // accepted
```

## Expectation

The two programs have the same linearization and the same declarations, so they should get the same verdict. Which verdict is a separate question:

- SLS §5.1.4: "a concrete definition always overrides an abstract definition", so both should compile, with `B.m` being `M.m`.
- scalac 2.13.18 accepts both. It emits a mixin forwarder `B.m` to `M.m`, and `(new B).m` returns `""`.
- javac rejects the Java analogue of both (`interface A extends M { String m(); }`, `class B implements A` and `class B implements M, A`): an abstract redeclaration in a subinterface hides the default (JLS §9.4.1, §8.4.8). JVM method selection (JVMS §5.4.6) agrees.

dotc agrees with javac on the first program and with scalac on the second. The difference seems to come from the deferred-member check considering a concrete member only when it is inherited from a direct parent.

A class that re-abstracts is rejected by both compilers whether or not the concrete trait is a direct parent (`trait M { def m: Int = 1 }; class A extends M; abstract class B extends A { def m: Int }; class C extends B with M`). Only traits behave differently.

Found by a Lean model of Scala's member rules: see [the witnesses](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala-types/ScalaTypes/Members.lean) `reabsTraitOnly` and `reabsTraitDirect`.
