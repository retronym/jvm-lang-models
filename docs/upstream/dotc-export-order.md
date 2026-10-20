# dotc: mutual wildcard exports compile or not by file order

Venue: scala/scala3 issue (area:export). Draft, not posted.

## Compiler version

3.9.0.

## Minimized code

```scala
// A.scala
object A { export B.*; def a = 1 }
// B.scala
object B { export A.a; def b = 2 }
```

## Output

`scala A.scala B.scala`:

```
-- [E120] Naming Error: A.scala:1:20 ------------------------------------------
1 |object A { export B.*; def a = 1 }
  |                    ^
  |Conflicting definitions:
  |def a: Int in object A at line 1 and
  |final def a: Int in object A at line 1
```

`scala B.scala A.scala` compiles. Compiling `A.scala` alone against the classfiles of the second build fails as the first did.

## Expectation

The same verdict in both orders.

## Why

`A`'s wildcard export reads `B`'s members (`membersBasedOnFlags` in `Namer.addWildcardForwarders`). `B`'s own export forwarders are entered while `B` completes. Typing `A.scala` first, `A`'s export completes `B`, which then has its forwarder `a`, so `A` exports `a` too and it clashes with `A.a`. Typing `B.scala` first, `B`'s export completes `A`, whose wildcard export reads `B`'s members while `B` is still completing and before its forwarder is entered, so `A` exports only `b`. `B`'s member set is a fact that grows while it is read; dotc guards the same situation for a sealed class's children (`ChildrenQueried`), not for members added by exports.

Related, not the same: [scala/scala3#10634](https://github.com/scala/scala3/issues/10634) (order of source files changed the result, fixed by invalidating member caches), [scala/scala3#25974](https://github.com/scala/scala3/issues/25974) (the order of exported methods in the classfile varies across sessions).

Found by the order-sensitivity harness of the jvm-lang-models Track L ([`order.py`](../../packages/scala/probes/forcing/order.py)); the model of a growing fact read without a freeze is [`Query.Freeze`](../../packages/query/Query/Freeze.lean), and this program is [`ScalaTypes.Laziness.exportOrder_reads_differ`](../../packages/scala-types/ScalaTypes/Laziness.lean#L275).
