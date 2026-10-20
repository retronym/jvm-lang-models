# Documents

Where to start, by goal; then four kinds of document, by what they are for. Per-package notes are in each package's `docs/`. Documents link every file, Lean name and GitHub reference they mention; [`scripts/lint_links.py`](../scripts/lint_links.py) checks this in CI (`--fix` writes the missing links).

## Start here, by goal

**Understand the theory.** Read [`packages/query/Query/Task.lean`](../packages/query/Query/Task.lean) (a compilation as a query tree with a trace), then [`packages/inc-comp/IncComp/Model.lean`](../packages/inc-comp/IncComp/Model.lean) (the specification's first page: `Compiler`, `Obligations`, `round`, `zinc`), then [`packages/inc-comp/IncComp/General.lean`](../packages/inc-comp/IncComp/General.lean) ([`XCompiler`](../packages/inc-comp/IncComp/General.lean#L22), where T2, T3a, T4 and T5 are proved once). [`packages/inc-comp/IncComp/Uniqueness.lean`](../packages/inc-comp/IncComp/Uniqueness.lean) and [`packages/zinc/Zinc/Loop/Cycles.lean`](../packages/zinc/Zinc/Loop/Cycles.lean) show when incremental equals clean and where it fails. The statements are in [`theorems.md`](theorems.md); [`specification.md`](specification.md) gives the rationale for the method.

**Start from a bug you know.** [`evidence/bug-map.md`](evidence/bug-map.md) maps 145 Zinc and compiler bugs to the part of the model that expresses them, or to a gap.

**Add a language feature to the Zinc model.** [`packages/zinc/Zinc/Features/Sam.lean`](../packages/zinc/Zinc/Features/Sam.lean) is the template: the compiler's algorithm as the unit task of a [`TCompiler`](../packages/inc-comp/IncComp/Tree.lean#L26), today's bridge as keys, the failing cases as witnesses ([`p1_today`](../packages/zinc/Zinc/Features/Sam.lean#L565), [`p2_today`](../packages/zinc/Zinc/Features/Sam.lean#L571)), the fix with `obligations_fix` and `fix_sound`. [`packages/zinc/docs/28-sam.md`](../packages/zinc/docs/28-sam.md) has the question behind it. The witnesses became scripted tests in [retronym/zinc#58](https://github.com/retronym/zinc/issues/58), which fail on `develop` as predicted. The gap clusters in [`evidence/bug-map.md`](evidence/bug-map.md) are the candidate features.

**Test Zinc.** The conformance harness (`sbt.internal.inc.bench.Conformance`, from [retronym/zinc#25](https://github.com/retronym/zinc/issues/25)) renders each program of a dump, applies each edit, and compares the incremental build's classfiles with a clean build's. `lake exe conformance` and `lake exe jconformance` write the dumps; the analysis scripts are in [`packages/harness/scripts/`](../packages/harness/scripts). The workflow is in [`packages/zinc/docs/10-names.md`](../packages/zinc/docs/10-names.md) and [`packages/zinc/docs/12-java.md`](../packages/zinc/docs/12-java.md); pending tests in [`evidence/tests.md`](evidence/tests.md).

**Maintain javac, scalac or dotc.** [`packages/java`](../packages/java), [`packages/scala`](../packages/scala) and [`packages/scala-types`](../packages/scala-types) state what the compilers emit for a subset, calibrated by the probes beside them. [`packages/scala/Scala/Facts.lean`](../packages/scala/Scala/Facts.lean) and the `comp` failures in the bug map are where joint and separate compilation differ.

**Maintain MiMa.** [`packages/mima`](../packages/mima): MiMa as a bridge design, its six gaps, corrected rules; [`packages/links`](../packages/links) connects it to Zinc (B4).

**Maintain the IntelliJ Scala plugin.** [`packages/intellij`](../packages/intellij): the theorems behind the plugin's substitutor checks, on top of `ScalaTypes.AsSeenFrom`.

## Current: what holds now

| document | read it to … |
|---|---|
| [`status.md`](status.md) | see, per package, what is proved for every program and what is checked on a space or calibrated against the real tool, with the bug-map counts and the trust checks |
| [`specification.md`](specification.md) | understand why the model is a specification of the compiler bridge, and the rules that follow (theorems vs `example`s, witnesses, calibration) |
| [`specification-ledger.md`](specification-ledger.md) | find, per JVMS, JLS and SLS section, the rules that cite it, the behaviour it leaves unspecified and the contradictions the calibrations found (generated) |
| [`stats.md`](stats.md) | see each package's size: Lean files, lines, theorems and checked examples (generated) |
| [`roadmap.md`](roadmap.md) | find open work on the JVM, Java, Scala and binary-compatibility layers |
| [`theorems.md`](theorems.md) | read the obligations and T1–T5, stated once, where their hypotheses bite, and the trust checks |

## Evidence: the bugs and tests the model is held against

| document | contents |
|---|---|
| [`evidence/bugs.md`](evidence/bugs.md) | 145 incremental-compilation bugs from Zinc's and the compilers' trackers, grouped by feature |
| [`evidence/tests.md`](evidence/tests.md) | Zinc's 208 scripted tests, grouped by the mechanism they exercise; pending and disabled ones with their families |
| [`evidence/bug-map.md`](evidence/bug-map.md) | each bug and each pending test mapped to the part of the model that expresses it, or to a gap; the gap clusters; predictions the model makes that no test covers yet |

Start from a bug you know: find it in `bug-map.md`, which names the Lean file and the theorem or witness.

## Per package

| package | notes |
|---|---|
| `zinc` | [one record per phase](../packages/zinc/docs/README.md), 10 to 31: the question, the design, the results; the index says what each phase proved and checked |
| `inc-comp` | [`framework-merge.md`](../packages/inc-comp/docs/framework-merge.md): how the four compiler variants became one [`XCompiler`](../packages/inc-comp/IncComp/General.lean#L22) |
| `jvm`, `java`, `scala`, `mima` | the calibration tracks: [`track-j.md`](../packages/jvm/docs/track-j.md), [`track-java.md`](../packages/java/docs/track-java.md), [`track-s.md`](../packages/scala/docs/track-s.md) (also Track N, binary names, designed in [`track-n-design.md`](../packages/scala/docs/track-n-design.md)), [`track-l.md`](../packages/scala/docs/track-l.md) (Track L, laziness, cycles and phase-indexed facts in scalac and dotc), [`track-b.md`](../packages/mima/docs/track-b.md) |

## History: how it got here

Kept as written; only their paths to other files were updated. The Zinc model started in retronym/talks (`zinc-incrementality/lean/`, moved here with its history from talks `b9058db`), the IntelliJ model in retronym/scala-type-system-tck (`lean/`, likewise).

| document | contents |
|---|---|
| [`history/phases.md`](history/phases.md) | the Zinc model's plan from 8 October 2026: the first two findings, the encoding choices, phases 1 to 9 in full |
| [`history/reviews/2026-10-11-morning.md`](history/reviews/2026-10-11-morning.md) | the first review of the framework, eight findings |
| [`history/reviews/2026-10-11-central.md`](history/reviews/2026-10-11-central.md) | the central review after the parallel work of 10 and 11 October: the model, the findings ledger, the talk and documents |
| [`history/reviews/2026-10-12-next-steps.md`](history/reviews/2026-10-12-next-steps.md) | a review of the whole plan after Track J6: gardening, quick wins, the mountains |
| [`history/reviews/2026-10-12-specifications.md`](history/reviews/2026-10-12-specifications.md) | turning the models on the specifications: soundness, omissions, contradictions |
| [`history/reviews/2026-10-16-refined-plan.md`](history/reviews/2026-10-16-refined-plan.md) | where the model is silent, prior art, ten ranked items |
| [`history/reviews/2026-10-16-merkle-slice.md`](history/reviews/2026-10-16-merkle-slice.md) | the decision ledger for the Merkle PoC and the instance that is Zinc |
| [`history/repository-split.md`](history/repository-split.md) | the plan for this repository and the record of the split into packages (step 8, in retronym/talks, still open) |
