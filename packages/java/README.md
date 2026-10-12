# `Java`

What javac emits for a Java subset: lowering to classfiles as a `Task`, constants folded (JLS §13.4.9; `lower_congr`), and JLS chapter 13's binary-compatibility rules checked against `jvm` linkage. No Mathlib.

**Start here.** `Java/Lower.lean`, then `Java/Jls13.lean`.

**Calibration.** `probes/probe.py` compiles the spaces with javac 17, 21 and 25: 99 programs agree. `docs/PLAN-track-java.md`.

**Gaps.** Java edits have not been run through MiMa (Track B3).

## Files

| File | Contents |
|---|---|
| `Java/Syntax.lean` | An attributed Java subset, as javac's back end sees it |
| `Java/Lower.lean` | Lowering to classfiles as a `Task`, constants folded (JLS §13.4.9); `lower_congr` |
| `Java/Space.lean` | Program spaces for calibrating lowering against javac |
| `Java/Catalogue.lean` | Java library edits, lowered and linked |
| `Java/Jls13.lean` | JLS chapter 13's rules, checked against `Jvm` linkage |
| `probes/probe.py` | Compiles `javaprobe`'s sources with javac per release and diffs the classfiles against the model |
