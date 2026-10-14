# Draft: scala/scala3 issue

**Tracker search (13 October 2026).** No report of this form. I searched scala/scala3 for bad bounds, conflicting bounds, unsound null, and "does not conform to upper bound". The closest are:

- [scala/scala3#23520](https://github.com/scala/scala3/issues/23520) (open): bad bounds in a refinement, inhabited by a recursive `val`.
- [scala/scala3#5854](https://github.com/scala/scala3/issues/5854) (closed): bad bounds in a refinement, through a not-yet-initialized path.
- [scala/scala3#15569](https://github.com/scala/scala3/issues/15569): it asked for "a compilation error on the definition of `Foo`" for `trait Foo[X >: Any <: Nothing]`, and was closed by [scala/scala3#15571](https://github.com/scala/scala3/pull/15571), which checks type *arguments* for bad bounds instead.
- [scala/bug#9633](https://github.com/scala/bug/issues/9633) (open, "should not compile"): the `null`-path hole for Scala 2, with two traits. It was noted as still compiling in 3.3.0-RC6.

**Title:** A type member's bounds are not checked at its declaration, so one trait and a `null` path give a ClassCastException

## Compiler version

3.9.0 and 3.10.0 (also with `-source future`).

## Minimized code

```scala
object Main {
  trait B { type L >: Int <: String }
  val p: B = null
  def up(x: Int): p.L = x
  def down(l: p.L): String = l
  def main(args: Array[String]): Unit = println(down(up(1)).length)
}
```

## Output

It compiles, and at run time:

```
java.lang.ClassCastException: class java.lang.Integer cannot be cast to class java.lang.String
```

The program has no cast, type test or pattern match.

## Expectation

The bounds `>: Int <: String` are inconsistent where they are written, and nothing about them depends on a path or a type argument. Scala 2 (2.12.21, 2.13.18) rejects the trait at the declaration:

```
error: lower bound Int does not conform to upper bound String
  trait B { type L >: Int <: String }
```

dotc reports the bounds only where the type is realized. `val p: B = new B {}` is rejected ("cannot be instantiated since it has a member L with possibly conflicting bounds Int <: ... <: String"), and so is a `lazy val` path. `null` is not a realization, so a `null` path of type `B` passes. `-Yexplicit-nulls` rejects `val p: B = null`, which closes this program but not the general rule.

The same holds for the other two places bounds are declared. Both compile in 3.9.0 and 3.10.0 and are rejected by Scala 2 at the declaration:

```scala
trait B[L >: Int <: String]                    // a type parameter
val p: { type L >: Int <: String } = null      // a refinement; then the same up/down throws
```

This is a smaller form of [scala/bug#9633](https://github.com/scala/bug/issues/9633) than the bug's own: no intersection is needed, because one declaration carries the conflict. The design of checking bounds at realization rather than declaration ([Scaling DOT to Scala: soundness](https://www.scala-lang.org/blog/2016/02/17/scaling-dot-soundness.html)) is about bounds that conflict only in combination, which a local check cannot see. Bounds that conflict where they are written can be seen locally, and Scala 2 does see them.

## Cause

`PostTyper` checks a type definition's bounds with `Checking.checkGoodBounds`, except where its owner is an abstract class or a trait:

```scala
if !sym.is(Param) && !sym.owner.isOneOf(AbstractOrTrait) then
  Checking.checkGoodBounds(tree.symbol)
```

The exemption was added on purpose, in scala/scala3 commit `a24915c9f6` (4 July 2022, alongside [scala/scala3#15571](https://github.com/scala/scala3/pull/15571)): "Don't check bounds for type definitions in abstract classes, traits, or refinements. Bounds violations will be detected when values of these types are created." The rationale assumes a path of type `B` is reached only through a value built by `new`, where `checkRealizableBounds` runs. `null` is a value of type `B` that was never created, so the violation is never detected.

## Suggested fix

Check a type member's, type parameter's and refinement member's declared bounds at the declaration (`lo <: hi`) in abstract classes and traits too, that is, drop `!sym.owner.isOneOf(AbstractOrTrait)` from the guard, as Scala 2 does and as [scala/scala3#15569](https://github.com/scala/scala3/issues/15569) first asked. A declaration's own bounds are known where it is written; only bounds that conflict in combination need realizability, which stays as it is. The tests the commit moved (`tests/init/neg/i11572.scala`, `tests/init/neg/i5854.scala`, `tests/neg-strict/i1050.scala`) are where the change would show.

Found by enumerating 2,430 small programs over type members, paths and views, compiling and running each on scalac 2.12.21, 2.13.18 and dotc 3.9.0, and calibrating a Lean model of the compilers' checks against them ([retronym/jvm-lang-models, Track T](https://github.com/retronym/jvm-lang-models/blob/main/packages/scala-types/docs/track-t.md)), with an LLM's help. dotc accepts 264 programs there that throw a cast-free `ClassCastException`. One family of them, which Scala 2 rejects at the declaration, has this shape.
