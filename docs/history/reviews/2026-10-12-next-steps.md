# Next steps, 12 October 2026

A review of the whole plan after Track J6, with three lists: gardening the model needs now, quick wins that the J6 method makes cheap, and the mountains. Facts checked against the tree at `c08ca87`; nothing here is implemented.

## Where it stands

- Every track's "done" is calibrated: HotSpot on 58,400 + 30,348 client programs, javac on 99, scalac/dotc on ~1,350 lowerings and 4,704 hierarchies, MiMa on 35 catalogue cases and 302 edits. Two model bugs in the JVM layer were found this week by *shape* (the JVMS's own example), not by the existing spaces. That is the main lesson: the spaces are enumerations over one shape each, and each new shape has found something.
- No open PRs in this repository; the four remote branches are all merged (0 ahead of `main`) and can be deleted, as can the local `claude/latest`.
- The upstream backlog is large: 10 drafts on retronym/zinc, 2 on sbt/zinc, 3 model-related on retronym/scala, 2 on retronym/scala3 (#10, #11), 4 MiMa issues, 1 TCK PR, and a dozen unrelated performance drafts. Nothing has moved from draft to upstream since 9 October except the MiMa issues.

## Gardening

Do these first; a day's work, and they make everything after cheaper.

1. **Generated numbers.** "45 library edits" and "58,400 programs" appear in `status.md`, the root and `jvm` READMEs, `Jvm/Spec.lean`, `roadmap.md` and `track-j.md`; the catalogue is past 45 and the program count is now 88,748 across four spaces. Extend `model_stats.py` (already CI-checked) to count catalogue cases and space sizes from a `lake exe jvmcases --count`, and cite the generated table instead of literals. Same for the Scala and Java probe counts.
2. **A calibration ledger.** Each probe run leaves nothing behind but a sentence in a track document. Record each run as a JSON line (commit, space, tool versions, program count, disagreement count, known-deviation list) under `packages/*/probes/runs/`, and have the docs cite it. Then `status.md` can say *when* a number was last true, and a model change that silently alters predictions on a calibrated space is visible: a script that re-dumps the verdicts and diffs them against the last run's recorded verdicts (the probe already emits per-program results; keep them).
3. **Calibration in CI, on demand.** The MiMa.Sound job is the pattern. A `workflow_dispatch` job with a Temurin 21/25 matrix (`setup-java`) that runs `probe.sh` over a chosen space and uploads the ledger line. Timing unknown; measure first.
4. **One space builder.** `space`, `space3`, `space5`, `chainSpace` and MiMa's `spaceB` are five hand-rolled `do`-enumerations with duplicated plumbing (`opt`, `tag`, `wellTyped`, site lists). Factor a builder: library shape × client shape × sites, named, with `wellTyped` applied once. J7 and J8 below become a few lines, and `MiMa.Fixed` and `Sound` can run over *any* space, not only `spaceB`.
5. **MiMa over the new spaces.** Track B1 compared MiMa on the 35 J1–J3 cases only. The J5 and J6 cases and the chain space have not been through `compare.py` or the MiMa model. Sixteen catalogue cases have `mima := none`; separate "MiMa is silent, confirmed" from "not run". Run `Fixed` over `chainSpace`: `methodBecomesFinalBehind` is package-private, so `Fixed` (public members only) is probably silent too, which is either a sixth gap or a documented scope line.
6. **Roadmap drift.** The Done table omits J6; "clients in the library's package" and "a space over two client classes" are listed as open J3 gaps, but `chainSpace` has both (`J` in package 1 or 2, `X` and `J`). Mark them done in `roadmap.md`, `track-j.md` and the [`Link.lean`](../../../packages/jvm/Jvm/Link.lean) header. Fold the "next seams" list into the roadmap so it does not live only in a chat transcript.
7. **Branch hygiene.** Delete the merged remote and local branches; keep `main` and the active worktree.
8. **Upstream triage.** Pick the two drafts with a model-predicted failing test and a one-paragraph fix ([retronym/zinc#57](https://github.com/retronym/zinc/issues/57) value-class forwarders, #58 givens/SAM) and open them on sbt/zinc; the rest stay drafts. One scala3 PR (#10, `NoInits`) carries Track B4 for Scala 3 and deserves a real PR with the model's witness as the test.

## Quick wins

Each is one shape, one space, one probe run, following J6. Expect each to take about a session and to have a fair chance of finding a rule.

- **J7: default methods along superinterface chains.** `I1 ← I2 ← I3`, each `m` default, abstract, static, private or absent, in package 1 or 2; a library class `C` implementing some of them, possibly declaring `m`; a client `X` below `C` or implementing directly; `invokeinterface` and `invokevirtual` sites. Exercises §5.4.3.3's maximally-specific selection, §5.4.6 step 2, and the JDK-8356942 region. Same size as the chain space.
- **J8: field resolution through superinterfaces at depth.** §5.4.3.2 looks in the class, then superinterfaces recursively, then the superclass. Fields named `m` in `A`, `B`, `I`, `J` at several levels, static or not, final or not, any access; `getfield`, `getstatic`, `putfield`, `putstatic`. This is where [scala-garden/mima#995](https://github.com/scala-garden/mima/issues/995) came from, and the model's rule there has one witness, not a space.
- **`Object`'s methods in interface resolution.** §5.4.3.4 step 2: an interface method reference to `hashCode` or `toString` resolves to `Object`'s. Needs `Object` in the class table with its public methods; a few catalogue cases and a column in J7's space. Small, and a standing gap in [`Link.lean`](../../../packages/jvm/Jvm/Link.lean).
- **Source-model remainders that unlock catalogue cases:** `var` and constructor parameters in the Scala model (setters are where the scalac 2 `AbstractMethodError` bug lives), `var` in Java. These widen Track B3 directly.

## Mountains

In order of how much they unlock.

1. **Track J4: behaviour.** Method bodies as a list of sites run when a method runs. It unlocks the 17 `ReversedMissingMethodProblem` reports, nestmates, folded constants, and the Scala `$init$` chain (the catalogue already notes that `valAddedToTrait` fails *earlier* on HotSpot than in the model, through `$init$`'s setter call: that is a behaviour gap showing up as a linkage inaccuracy). Design document first: the trace of a run, how `changesSomeClient` generalises, and what the probe compares (the sequence of methods entered, from `ProbeLog`).
2. **A real-classfile importer.** A Classfile-API tool that reads a JAR into [`Jvm.World`](../../../packages/jvm/Jvm/Link.lean#L74) as JSON, and a Lean reader. Three uses, each big: run the MiMa model and `Fixed` against MiMa on real library pairs (two scala-library or Guava releases) and treat every difference as a model bug or a MiMa gap; translation validation of lowering against a real build's classfiles, as `IncBench --verify` did for Zinc; and real libraries as the `v0` of client spaces. This is the step from "spaces" to "the world", and the strongest argument the model can make to maintainers.
3. **The general soundness proof for `Fixed`.** [`miss_changes_footprint`](../../../packages/mima/MiMa/Keys.lean#L71) already gives: a miss is a changed footprint query. The proof is per query kind: for each of resolution, selection and access, show that `Fixed`'s key covers it and reports when the answer changes. Start with method resolution through a public class, the kind MiMa-M1 is about; it is the monotonicity lemma over superclass walks that the roadmap names. Worth a design note on the statement before any Lean.
4. **A long-lived compiler harness.** The prerequisite for Track B3 at scale and for calibrating `Members` on the 216,000-program `FlatRules` space. javac first: `javax.tools` in process is a few dozen lines and sets the protocol (program in, diagnostics and classfile digests out); then `nsc.Global` reuse as the TCK's reference engine does; dotc last.
5. **Port `Hier`, `Erasure`, `Flat`, `ImplicitScope` onto the shared Scala layer.** The coherence mountain: until these four import `ScalaTypes` and `Scala.Lower`, the repository has two Scala semantics, and every rule the probes correct in `Members` or `Lower` is not reflected in the Zinc instances. Single-writer. Start with `Hier` (457 lines, the smallest) as the template, keeping its theorems; `FlatShared` already shows the comparison technique.
6. **Track B3: source edit spaces.** After 4. The Java catalogue has never been through MiMa; that alone is an afternoon with the existing probes and should come before the harness.

## Suggested order

Gardening 1–7 in one session. Then J7 and J8 on the factored builder, with the ledger recording their runs. Then the J4 design document for review. The importer and the harness are each a design document before code; the proof and the port are single-writer and can run beside the probe work.
