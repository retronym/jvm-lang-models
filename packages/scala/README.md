# `Scala`

What scalac and dotc emit for a Scala subset: lowering to classfiles as a `Task` (forwarders, bridges, `$init$`, erasure; `lower_congr`), the binary names of classes and objects, program spaces for calibration, and a catalogue of library edits lowered and linked by `jvm`. No Mathlib.

**Start here.** [`Scala/Lower.lean`](Scala/Lower.lean).

**Calibration.** [`probes/probe.py`](probes/probe.py) compiles the spaces with scalac 2.12, 2.13 and dotc 3 and diffs the classfiles: 1,353 programs agree for 2.12 and 2.13, 1,368 for 3.9. [`probes/names.py`](probes/names.py) does the same for binary names, local and anonymous classes included: 453 for 2.12 and 2.13, 471 for 3.9. [`docs/track-s.md`](docs/track-s.md).

**Gaps.** Case classes with type parameters or several parameter lists, objects nested in classes, local and anonymous classes, overloading, Java-defined parents ([`docs/roadmap.md`](../../docs/roadmap.md) at the repository root).

## Files

| File | Contents |
|---|---|
| [`Scala/Lower.lean`](Scala/Lower.lean) | Lowering to classfiles as a `Task` (forwarders, bridges, `$init$`, erasure); `lower_congr` |
| [`Scala/Facts.lean`](Scala/Facts.lean) | F6 as a compositionality failure, by kernel `decide` |
| [`Scala/Space.lean`](Scala/Space.lean) | Program spaces for calibrating lowering against scalac and dotc |
| [`Scala/Catalogue.lean`](Scala/Catalogue.lean) | Scala library edits, lowered and linked: before, after, fresh |
| [`Scala/Names.lean`](Scala/Names.lean) | Binary names of classes, traits and objects, member, local and anonymous, and their own `InnerClasses` entries, per compiler version; their program space (Track N) |
| [`Scala/Md5.lean`](Scala/Md5.lean) | MD5, as the compilers print it when they shorten a long class name |
| [`probes/probe.py`](probes/probe.py) | Compiles `scalaprobe`'s sources with scalac 2.12, 2.13 and 3 and diffs the classfiles against the model |
| [`probes/names.py`](probes/names.py) | Compiles `namesprobe`'s programs with scalac 2.12, 2.13 and 3 and compares classfile names and `InnerClasses` entries with `Names` |
| [`probes/forcing/`](probes/forcing) | Track L ([`docs/track-l.md`](docs/track-l.md)): forcing footprints with spy completers (`Footprint2.scala`, `Footprint3.scala`), phase-indexed facts of a real run (`Phases2.scala`, `Phases3.scala`), the cycle battery (`battery.py`, 24 programs, 2.12/2.13/3) and the order-sensitivity harness (`order.py`, 26 multi-file programs in both file orders and recompiled file by file) |
| [`probes/run.py`](probes/run.py) | Runs the catalogue's clients on HotSpot (scalac-compiled, instrumented) and compares outcomes with the model |
| [`probes/members.py`](probes/members.py) | Calibrates [`packages/scala-types/ScalaTypes/Members.lean`](../scala-types/ScalaTypes/Members.lean) against scalac's and dotc's override errors |
