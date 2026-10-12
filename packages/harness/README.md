# `Harness`

The executables that enumerate program spaces, write the dumps the conformance harness and the probes read, and print the exhaustive checks' tables; and the scripts that analyse the runs. Run them from the repository root: `lake exe <name>`.

**Start here.** `lake exe exhaustive erasure` (about 45 s) prints the erasure table of `zinc`'s [`Erasure.lean`](../zinc/Zinc/Features/Erasure.lean).

**Calibration.** These are the calibration drivers; each probe lives with its layer (`packages/*/probes`).

**Gaps.** None specific.

## Files

| File | Contents |
|---|---|
| [`Harness/Exhaustive.lean`](Harness/Exhaustive.lean) | `lake exe exhaustive [erasure\|implicit\|composed\|pingpong\|flatshared\|v]`: the bounded exhaustive checks, natively |
| [`Harness/Conformance.lean`](Harness/Conformance.lean) | `lake exe conformance`: the `FlatRules`, names, givens, inline and opaque spaces with verdicts, for the harness; `conformance cost` tabulates soundness and precision per mode |
| [`Harness/JConformance.lean`](Harness/JConformance.lean) | `lake exe jconformance names\|sealed …`: the Java spaces, for the harness |
| [`Harness/JvmCases.lean`](Harness/JvmCases.lean) | `lake exe jvmcases [space\|verdicts]`: the JVM catalogue, for [`packages/jvm/probes`](../jvm/probes) |
| [`Harness/ScalaProbe.lean`](Harness/ScalaProbe.lean) | `lake exe scalaprobe OUT`: Scala sources and the model's classfiles, for [`packages/scala/probes`](../scala/probes) |
| [`Harness/JavaProbe.lean`](Harness/JavaProbe.lean) | `lake exe javaprobe OUT`: Java sources and the model's classfiles, for [`packages/java/probes`](../java/probes) |
| [`Harness/MimaMain.lean`](Harness/MimaMain.lean) | `lake exe bincompat edits\|mima\|gaps\|scala\|verdicts`: the edit space and MiMa verdicts, for [`packages/mima/probes`](../mima/probes) |
| [`server/`](server) | The compile server ([design](docs/compile-server.md)): `Server.java` reads JSON-lines requests (compile, run) and keeps one compiler warm, over pipes only; `JavacBackend.java` is javac through `javax.tools`, `ScalacBackend.scala` scalac 2 with a cached `Global`, `DotcBackend.java` dotc with a cached `ContextBase` |
| [`scripts/compiler.py`](scripts/compiler.py) | The probes' client for the compile server: builds it on first use, starts one per JDK or compiler version, compiles and runs programs one at a time; `python3 -I compiler.py scala VERSION SRC OUT ...` from the shell |
| [`scripts/select.py`](scripts/select.py), `jselect.py` | Pick bases from a `conformance names` or `jconformance names` dump until every signature has an edit |
| [`scripts/analyse.py`](scripts/analyse.py), `janalyse.py` | Compare a harness run of the names or Java spaces with the model: resolution, verdict, recompiled sets, divergences |
| [`scripts/inline_opaque.py`](scripts/inline_opaque.py) | The same for the inline and opaque spaces |
| [`scripts/families.py`](scripts/families.py) | The names space's divergence families, for `analyse.py` and `modelcount.py` |
| [`scripts/modelcount.py`](scripts/modelcount.py) | Counts the edits of a dump that the model calls unclean, by family |
