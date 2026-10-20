# dotc shortens a class name before encoding it

Venue: scala/scala3 issue (area:backend). Draft, not posted.

## Compiler version

3.9.0. scalac 2.12.21 and 2.13.18 for comparison.

## Minimized code

```scala
package p
object O { class `++++++++++++++++++++++++++++++++++++++++++++++++++` }
```

## Output

scalac 2.13.18 writes `p/O$$plus$plus…$$$$<md5>$$$$…$plus.class`: the encoded flat name, `O$` and fifty `$plus`, is 252 characters, over 2.13's limit of 233, so `compactify` shortens it.

dotc 3.9.0:

```
error: error writing …/p/O$$plus$plus…$plus.class: java.nio.file.FileSystemException: …
error: unable to write …/A.scala java.lang.NullPointerException: tried to cast away nullability, but value is null
```

## Expectation

The same shortening as scalac, which [scala/scala3#11279](https://github.com/scala/scala3/pull/11279) set out to replicate.

## Why

`SymDenotation.fullNameSeparated` compactifies the qualified *source* name (`O$++…+`, 52 characters, under the limit), and the backend encodes it afterwards (`mangledString`). scalac's names are encoded when parsed, so its `compactify` sees the encoded length. Any name with operator characters or characters outside Java identifiers can cross the limit after the check. For the same reason the MD5 and the kept prefix and suffix are of the source name, so where both compilers shorten, dotc's name differs from scalac's (expected, as the encodings differ anyway, but worth stating).

A second, smaller point: dotc's `MaxNameLength` is `240 - 6` (`.class`), scalac 2.13's `240 - 7`, which also reserves the module class's `$` ([scala/bug#8199](https://github.com/scala/bug/issues/8199)). A nested object whose flat name is 234 characters gets a 241-character file name from dotc. (Read from the sources; not reproduced here, since 241 is within macOS's and Linux's limit.)

Found by calibrating a model of binary names against both compilers: [`Scala.Names`](../../packages/scala/Scala/Names.lean), [`names.py`](../../packages/scala/probes/names.py).
