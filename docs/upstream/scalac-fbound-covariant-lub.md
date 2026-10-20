# scalac: the inferred join of two covariant F-bounded classes violates the F-bound

Venue: scala/bug. Draft, not posted. Found by the Track LUB probe ([`packages/scala-types/probes/lub`](../../packages/scala-types/probes/lub), world `fboundco`).

## Compiler version

2.12.21 and 2.13.18. dotc 3.9.0 compiles it.

## Minimized code

```scala
trait Fb[+T <: Fb[T]]
class Fa extends Fb[Fa]
class Fc extends Fb[Fc]
object Test {
  def c: Boolean = true
  val x = if (c) new Fa else new Fc
}
```

## Output

```
a.scala:6: error: type arguments [Fb[Object]] do not conform to trait Fb's type parameter bounds [+T <: Fb[T]]
  val x = if (c) new Fa else new Fc
      ^
```

`-Vprint:typer` shows `private[this] val x: Fb[Fb[Object]]`. `List(new Fa, new Fc)` fails the same way (`List[Fb[Fb[Object]]]`).

## Expectation

The program compiles: `x` has a well-formed upper bound of `Fa` and `Fc`. dotc 3.9.0 infers `Fb[Fa | Fc]`, which conforms because `Fa | Fc <: Fb[Fa | Fc]` by covariance. scalac's `lub` has no union to fall back on; the exact join `Fb[Fb[Fb[…]]]` is infinite, and the depth limit (`lubDepth`) cuts it off by putting `Object` (the `lub` at depth zero) in the innermost argument. The cut-off type is a supertype of both branches but is not well-bounded, and refchecks rejects it.

The invariant variant (`trait Fb[T <: Fb[T]]`) is accepted by scalac, as an existential `Fb[_ >: Fa with Fc <: Fb[_ >: Fa with Fc <: Object]]`, whose innermost bound is also `Object`, but as a wildcard's bound, and that is accepted. dotc rejects that one ([scala/scala3#9941](https://github.com/scala/scala3/issues/9941), open): each compiler rejects the other's well-typed program.

## Notes

A possible fix: when the truncated argument would violate the parameter's bound, fall back to an existential with that bound (`Fb[_ <: Fb[_]]`, as for the invariant case), or to the parameter's bound itself. An explicit `val x: Fb[Fb[_]] = …` is rejected for the same reason; `Fb[_]` and `Fb[_ <: Fb[_]]` are accepted (checked on 2.13.18), so the workaround is an annotation.
