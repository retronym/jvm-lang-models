# Draft: contributors.scala-lang.org discussion

**Title:** What should re-abstraction mean in Scala?

When a trait or class re-declares as abstract a member that it inherits concretely, there are currently four answers to whether a subclass still has to implement it:

| | class re-abstracts | trait re-abstracts | trait re-abstracts, concrete trait a direct parent |
|---|---|---|---|
| SLS §5.1.4 ("a concrete definition always overrides an abstract definition") | no | no | no |
| scalac 2.13 | yes | no (mixin forwarder to the concrete member) | no |
| dotc 3.9 | yes | yes | no |
| javac (JLS §9.4.1, §8.4.8) and JVM selection (JVMS §5.4.6) | yes | yes | yes |

Programs:

```scala
// class re-abstracts: rejected by 2.13 and 3.9
trait M { def m: Int = 1 }
class A extends M
abstract class B extends A { def m: Int }
class C extends B with M

// trait re-abstracts: 2.13 accepts (B.m forwards to M.m), 3.9 rejects
trait M { def m: String = "" }
trait A extends M { def m: String }
class B extends A

// same, M also a direct parent: both accept
class B extends M with A
```

Some questions:

- Is re-abstraction a feature? Java treats it as one (an interface can withdraw a default), and the class case in both compilers matches. The spec sentence predates traits with concrete members re-declared abstract.
- Should a trait be able to re-abstract? The 2.13 answer makes the abstract declaration in `A` a no-op for any class that mixes in `A`. The Scala 3 answer makes it a real obligation, but one that a direct `M` parent discharges, which the linearization doesn't explain.
- Cross-building: a library that compiles on 2.13 can fail on 3 with "needs to be abstract", and the fix (adding the concrete trait as a direct parent) is not obvious.

The four rules come from a Lean model of the member rules, calibrated against the compilers on a generated space of small programs: [Members.lean](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala-types/ScalaTypes/Members.lean), and the account in [track-s.md](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala/docs/track-s.md).
