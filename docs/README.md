# Documents

Four kinds of document, by what they are for. Per-package notes are in each package's `docs/`.

## Current: what holds now

| document | read it to … |
|---|---|
| [`status.md`](status.md) | see, per package, what is proved for every program and what is checked on a space or calibrated against the real tool, with the bug-map counts and the trust checks |
| [`specification.md`](specification.md) | understand why the model is a specification of the compiler bridge, and the rules that follow (theorems vs `example`s, witnesses, calibration) |
| [`roadmap.md`](roadmap.md) | find open work on the JVM, Java, Scala and binary-compatibility layers |
| [the root README](../README.md#the-theorems) | read the obligations and T1–T5, stated once |

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
| `zinc` | [one record per phase](../packages/zinc/docs/README.md), 10 to 28: the question, the design, the results; the index says what each phase proved and checked |
| `inc-comp` | [`framework-merge.md`](../packages/inc-comp/docs/framework-merge.md): how the four compiler variants became one [`XCompiler`](../packages/inc-comp/IncComp/General.lean#L22) |
| `jvm`, `java`, `scala`, `mima` | the calibration tracks: [`track-j.md`](../packages/jvm/docs/track-j.md), [`track-java.md`](../packages/java/docs/track-java.md), [`track-s.md`](../packages/scala/docs/track-s.md), [`track-b.md`](../packages/mima/docs/track-b.md) |

## History: how it got here

Kept as written; only their paths to other files were updated.

| document | contents |
|---|---|
| [`history/phases.md`](history/phases.md) | the Zinc model's plan from 8 October 2026: the first two findings, the encoding choices, phases 1 to 9 in full |
| [`history/reviews/2026-10-11-morning.md`](history/reviews/2026-10-11-morning.md) | the first review of the framework, eight findings |
| [`history/reviews/2026-10-11-central.md`](history/reviews/2026-10-11-central.md) | the central review after the parallel work of 10 and 11 October: the model, the findings ledger, the talk and documents |
| [`history/repository-split.md`](history/repository-split.md) | the plan for this repository and the record of the split into packages (step 8, in retronym/talks, still open) |
