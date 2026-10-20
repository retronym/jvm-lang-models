# dotc: what a wildcard export exports depends on file order

Venue: scala/scala3 issue (area:export). Draft, not posted. Two programs; the first is the more serious, since nothing reports it.

## 1. An exported member silently missing

```scala
// A.scala
object A { export B.*; def a = 1 }
// B.scala
object B { def b = A.a + 1 }
```

`scala A.scala B.scala`: `A` has the forwarder `b` (`javap`: `A$.b()` and the static forwarder `A.b()`). `scala B.scala A.scala`: no error, and `A` has no `b`: `A$` has only `a`. A client calling `A.b` compiles against one build and not the other; compiled separately against the first, it throws `NoSuchMethodError` against the second. Typing `B.scala` first, `b`'s inferred type types `A.a`, which completes `A`, whose wildcard export reads `B`'s members while `b` is still being completed, and leaves `b` out. (Where it is left out was not traced; no cyclic reference is reported.) The same with three objects (`export B.*` in `A`, `export C.c` in `B`, `export A.a` in `C`): two of the six file orders give `A` different members.

## 2. Mutual wildcard exports compile or not

The original report follows.

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

Found by the order-sensitivity harness of the jvm-lang-models Track L ([`order.py`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/packages/scala/probes/forcing/order.py)); the model of a growing fact read without a freeze is [`Query.Freeze`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/packages/query/Query/Freeze.lean), and this program is [`ScalaTypes.Laziness.exportOrder_reads_differ`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/packages/scala-types/ScalaTypes/Laziness.lean#L275).
