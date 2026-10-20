# scalac: an early phase travel freezes a class's binary name

Venue: scala/scala PR (or scala/bug issue, area:compiler). Draft, not posted. Latent: nothing in scalac or Zinc triggers it. A compiler plugin or macro that asks for a nested or local class's binary name before flatten changes the classfile names the run emits.

## Reproduction

A plugin phase after `pickler` that asks, for every class the unit defines, one of:

1. `enteringPhase(currentRun.flattenPhase.next)(cls.fullName('.'))` (what Zinc's [`ClassName.flatname`](https://github.com/sbt/zinc/blob/v1.10.8/internal/compiler-bridge/src/main/scala/xsbt/ClassName.scala#L26-L27) does);
2. `cls.javaBinaryNameString`.

```scala
class C
object C { def m: AnyRef = { class E; new E } }
```

With scalac 2.13.18:

| query | classfiles |
|---|---|
| none | `C.class C$.class C$E$1.class` |
| 1 | `C.class C$.class m$E.class` (`C$`'s InnerClasses: `E$1=class m$E`; `C.m.getClass.getName` is `m$E`) |

For `package p; class A { class Inner; def m = { class L; ... }; object O }`, query 2 gives `p/A/Inner.class`, `p/A/L.class`, `p/A/O$.class`.

The probe is [`Eager2.scala`](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala/probes/phases/Eager2.scala) (`-Dforce=flatten -Dkind=name`, and `-Dforce=typer -Dkind=binary`).

## Cause

Both names are memoized on the symbol at their first read:

* [`ClassSymbol.flattenedName`](https://github.com/scala/scala/blob/v2.13.18/src/reflect/scala/reflect/internal/Symbols.scala#L3469-L3473) caches `tpnme.flattenedName(rawowner, rawname)` the first time the name is asked at a phase with `flatClasses`;
* [`javaBinaryNameString`](https://github.com/scala/scala/blob/v2.13.18/src/reflect/scala/reflect/internal/Symbols.scala#L1302-L1307) caches `fullName('/', moduleSuffix)` the first time it is asked, at any phase.

The inputs are overwritten later in the run: LambdaLift re-owns a local class to its enclosing class and renames it (`E` to `E$1`). The flatten phase's view is correct once flatten has run. A phase travel can ask about that view before LambdaLift has run, and the cache keeps that answer.

The guard has to be on the phase the run has reached (`globalPhase`), not on the phase the question is about (`phase`):

```scala
override protected[this] def flattenedName: TypeName =
  if (flatname ne null) flatname
  else {
    val n = tpnme.flattenedName(rawowner, rawname)
    if (isPastLambdaLift(globalPhase)) flatname = n // or: assert, to find the early caller
    n
  }
```

The same applies to `javaBinaryNameString`: cache only once `globalPhase` is past flatten, or past LambdaLift for a class whose owner is a term. An answer computed early is still wrong for local classes, since their name is not yet decided. An assertion (`devWarning`) would name the caller.

## Context

The memoized name is a fact frozen at its first read without a guard, the pattern [Track L](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala/docs/track-l.md) models as `Query.Freeze` ([`flatname_early`](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala-types/ScalaTypes/Scopes.lean)). Forcing *infos* at later phases early has related effects. The scope copies an info transformer makes miss entries made afterwards, so `ScalaInlineInfo` lacks lifted methods, and outer fields that Constructors would drop survive ([track-p.md](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala/docs/track-p.md)).
