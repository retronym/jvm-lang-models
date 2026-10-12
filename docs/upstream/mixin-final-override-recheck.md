# Note: 2.13 re-checks overriding pairs across mixins (intentional)

Checking the shared semantics against the toy of Flat showed scalac 2.13 reporting override errors that 2.12 does not. The question was whether this is a 2.13 bug. It is not: it is [scala/scala#7439](https://github.com/scala/scala/pull/7439) ("Stricter refchecks: subclassing on traits does not imply suffixing for their linearisations", 2.13.0-RC1), which fixes [scala/bug#11136](https://github.com/scala/bug/issues/11136). The 2.12 backport, [scala/scala#7746](https://github.com/scala/scala/pull/7746), was closed unmerged.

The program from [scala/bug#11136](https://github.com/scala/bug/issues/11136):

```scala
trait IO { def c(x: Int): Int = 1 }
trait SO extends IO { override final def c(x: Int): Int = 2 }
trait SOIO extends IO { override def c(x: Int): Int = 3 }
trait SOSO extends SOIO with SO
abstract class AS extends SO
class L extends AS with SOSO
object Main { def main(a: Array[String]): Unit = println((new L).c(0)) }
```

| | result |
|---|---|
| scalac 2.12.21 | compiles; at run time `java.lang.IncompatibleClassChangeError: class L overrides final method AS.c(I)I` |
| scalac 2.13.18 | error: cannot override final member |
| dotc 3.9.0 | error: overriding method c in trait SO … cannot override final member |

The model ([`Scala.Members.recheck11136`](../../packages/scala-types/ScalaTypes/Members.lean#L631)) gives no error for 2.12 and `finalOverride` on `L` for 2.13 and for Scala 3. dotc re-checks the pair for the same reason as 2.13, by another rule: its cursor leaves a pair to a parent only if the parent has the two owners in the same linearization order (`canBeHandledByParent`, scala/scala3 neg/i5094), where 2.13 leaves none. Nothing to report upstream.
