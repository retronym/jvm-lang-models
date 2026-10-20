# scalac: an uncaught TypeError for a refinement of a class in its own F-bounded parent

Venue: scala/bug, possibly as a standalone reproduction on [scala/bug#11880](https://github.com/scala/bug/issues/11880) (closed, a 2.12 crash with the same `TypeError` on a `<refinement>`, reported without a standalone reproduction). Draft, not posted.

## Compiler version

2.12.21 and 2.13.18.

## Minimized code

```scala
class D[A <: D[A]]
class C extends D[C { def x: Int }]
```

## Output

```
A.scala:2: error: illegal cyclic reference involving class C
A.scala:2: error: illegal cyclic reference involving <refinement of C>
error: scala.reflect.internal.Types$TypeError: illegal cyclic reference involving <refinement of C>
Exception in thread "main" scala.reflect.internal.Types$TypeError: illegal cyclic reference involving <refinement of C>
```

Without the F-bound (`class D[A]`) scalac reports the two errors and exits normally.

## Expectation

No crash. Scala 3.9.0 compiles the program, so the cyclic reference itself is spurious ([scala/bug#8649](https://github.com/scala/bug/issues/8649) is the open report for that family, labelled "fixed in Scala 3"). Only the F-bound makes the difference between an error and a crash, which points at the check of the bound `C { def x: Int } <: D[C { def x: Int }]`, made while `C`'s parents are being typed, as where the `TypeError` escapes; not traced further.

Found by the cycle battery of the jvm-lang-models Track L ([`battery.py`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/packages/scala/probes/forcing/battery.py), `fb-parent-refines-self`).
