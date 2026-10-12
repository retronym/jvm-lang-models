# `Scala`

What scalac and dotc emit for a Scala subset: lowering to classfiles as a `Task` (forwarders, bridges, `$init$`, erasure; `lower_congr`), program spaces for calibration, and a catalogue of library edits lowered and linked by `jvm`. No Mathlib.

**Start here.** `Scala/Lower.lean`.

**Calibration.** `probes/probe.py` compiles the spaces with scalac 2.12, 2.13 and dotc 3 and diffs the classfiles: 1,348 programs agree for 2.12 and 2.13, 1,363 for 3.9. `docs/PLAN-track-s.md`.

**Gaps.** Case classes with type parameters or several parameter lists, nested and local classes, overloading, Java-defined parents (`docs/ROADMAP.md` at the repository root).

## Files

| File | Contents |
|---|---|
| `Scala/Lower.lean` | Lowering to classfiles as a `Task` (forwarders, bridges, `$init$`, erasure); `lower_congr` |
| `Scala/Facts.lean` | F6 as a compositionality failure, by kernel `decide` |
| `Scala/Space.lean` | Program spaces for calibrating lowering against scalac and dotc |
| `Scala/Catalogue.lean` | Scala library edits, lowered and linked: before, after, fresh |
| `probes/probe.py` | Compiles `scalaprobe`'s sources with scalac 2.12, 2.13 and 3 and diffs the classfiles against the model |
| `probes/members.py` | Calibrates `packages/scala-types/ScalaTypes/Members.lean` against scalac's and dotc's override errors |
