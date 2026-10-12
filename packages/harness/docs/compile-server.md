# A warm compiler server for the calibration probes

Design, 12 October 2026. For review before any code.

## Problem

Every probe pays for a cold compiler. [`packages/scala/probes/members.py`](../../scala/probes/members.py) batches a space into one `scala-cli compile --server=false` per compiler and needs *rounds*, because one program's error stops refchecks for the whole batch; the programs that erred are dropped and the rest recompiled until a run is clean. [`packages/scala/probes/probe.py`](../../scala/probes/probe.py) compiles 1,348 programs in one run per dialect and two for separate compilation. [`packages/mima/probes/scala.sh`](../../mima/probes/scala.sh) launches `scala.tools.nsc.Main` once per catalogue case. The runtime check in `members.py` compiles and runs one `Main` over every accepted program, so one bad program breaks the run for all.

Three costs follow:

- **Size.** The calibrated spaces stop at a few thousand programs, while the exhaustive checks run over hundreds of thousands (`FlatRules` has 216,000, and comparing it with `Members` found two gaps the 4,704-program calibration space never reached). The shared semantics is checked against scalac only where the batch cost allowed.
- **Batching artefacts.** A per-program result depends on which programs shared its run: error recovery in one unit, name clashes, and the round in which a program was compiled. The probes work around this with unique package names and rounds; neither is what a user's compiler sees.
- **No per-program timing or isolation.** A compiler crash, a timeout, or a non-deterministic result is attributed to a batch.

## What it is

One long-lived JVM per compiler version, started once per probe run and kept warm: it reads a program on stdin (sources, options, optional classpath of earlier outputs), compiles it in a fresh run of a reused compiler instance, and answers with the diagnostics and the classfiles. Each program is compiled on its own, so an error in one cannot hide another's. The probes talk to the servers instead of spawning compilers.

Prior art: Zinc's `CachedCompiler` keeps one `nsc.Global` and does `new Run` per compile; the TCK's reference engine (`retronym/scala-type-system-tck`, `reference/ScalacEngine.scala`) embeds `Global` with a `StoreReporter` and a `VirtualDirectory`; Bloop and scala-cli's build server keep compilers warm for builds; javac's `javax.tools` API is in-process by design.

## Key decisions

**Reuse the JVM and the JIT; reuse the compiler instance where its author does.** The dominant cost is JVM start-up and a cold JIT, not instance construction. For scalac 2, reuse `Global` and do `new Run` per program, as Zinc does. For dotc, a fresh `Compiler` and `Context` per program under one `ContextBase`, as the sbt bridge does; a reused base only if measurement says it matters. For javac, `ToolProvider.getSystemJavaCompiler()` per program, which is already in-process. Each is a knob, not a commitment.

**One program per run, unique package per program, recycle the instance.** Compiling each program in its own run removes the rounds and the batching artefacts. A reused `Global` keeps the previous run's top-level symbols in its root mirror, so programs keep their unique package names (the probes already generate `qN`), and the server recycles its instance every N programs (and on any crash) so memory and stale state are bounded. An order-independence check is part of the acceptance: a shuffled sample must give the same per-program results as the ordered run.

**Separate compilation gets a fresh instance.** A request may put earlier outputs on the classpath. Changing the classpath of a reused `Global` needs `invalidateClassPathEntries`, which exists for the IDE case but is a known source of subtle bugs. Today's separate-compilation cases are a handful, so the server uses a fresh instance for any request with a classpath. If separate-compilation spaces grow, invalidation becomes an optimisation to measure.

**Run in-process too.** The runtime check (which owner's `m` ran, what `Throwable` a client throws) loads the program's classes in a throwaway `URLClassLoader` and invokes `main`, capturing stdout. This replaces `members.py`'s single `Main` over every program and could later take over [`packages/jvm/probes/Run.java`](../../jvm/probes/Run.java)'s loop. One bad program breaks only itself; a timeout per run is possible.

**The protocol is JSON lines, like the JVM probe.** One request per line: an id, the sources by file name, compiler options, an optional classpath of ids (earlier outputs the server kept) or directories, and an operation (`compile`, `run`). One response per line: the id, the diagnostics as (file, line, column, severity, message), the output directory the server wrote the classfiles to, stdout for `run`, and wall-clock time. Classfiles stay on disk, since the probes already parse them from disk; the response carries a digest per class so a probe can skip reading when it only needs equality. [`Json.java`](../../jvm/probes/Json.java) is the dependency-free reader the JVM probe uses and can be shared.

**Parallelism is a pool inside one JVM.** A compiler instance is single-threaded; K instances in one JVM share the JIT. Start with K = 1 and measure; the pool size is a flag. Across compiler versions the servers are independent processes, one per version (scalac 2.12, 2.13, dotc 3.x, and one per JDK for javac, since `javac 25 --release 17` is not javac 17).

**What does not change.** The Lean side still enumerates spaces and prints sources and expected results (`lake exe scalaprobe`, `javaprobe`, `bincompat`); the probes still diff. The server is a transport, not a new oracle, and the first acceptance test is that it reproduces today's batch results exactly on the existing spaces.

## Risks

- **State leaking between runs on a reused `Global`.** Mitigated by unique packages, recycling, and the order-independence check; the fallback is a fresh `Global` per program, which still keeps the JVM and JIT.
- **Diagnostics differ between the batch and the single-program run.** Expected where the batch hid errors (that was the bug); every other difference is a finding about the probe's parser or the compiler, and goes in the track document.
- **Version drift.** The server pins compiler versions through coursier or scala-cli exactly as the probes do today; the calibration ledger records them per run.

## Steps

1. **javac server.** Smallest, sets the protocol and the Python client (`packages/harness/scripts/compiler.py`). Switch [`packages/java/probes/probe.py`](../../java/probes/probe.py) to it; results must equal today's on the 99 programs.
2. **scalac 2 server** with a cached `Global`. Differential check against the batch results on the membership space (4,704 programs, both 2.12.21 and 2.13.18), then switch `members.py` (dropping the rounds) and `probe.py`.
3. **dotc server.** Same check on 3.9.0.
4. **`run` in-process.** Switch the runtime check in `members.py` and the per-case compile in `scala.sh`.
5. **Scale.** `Members` against scalac and dotc on the `FlatRules` 216,000 programs and `HierShared`'s space: the calibration this exists to enable, with the findings in [`packages/scala/docs/track-s.md`](../../scala/docs/track-s.md).

Future work: MiMa in-process (its probe is already a Scala program); the Zinc conformance harness keeps its own compiler handling.
