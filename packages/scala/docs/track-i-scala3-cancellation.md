# Track I — Cancellation for the Scala 3 presentation compiler: design and spike

22 October 2026. Builds on [track-i.md](track-i.md) (§2 for the survey, §7 and §9 for the model, §11 for the abort theorems).

## Summary for a busy reader

dotc under Metals never interrupts a running request: there is no presentation-compiler thread to interrupt, the interrupt bit is swallowed at the only checkpoints there are (unit and subphase boundaries), and a timeout throws the whole driver away while the old job keeps running on it. Every request retypes its file from scratch, which is what makes the design safe, and what makes it slow on a large file. This note designs the cheapest robust cancellation for it, **abort and restart**: a request waiting while the compiler types unwinds the run at the next tree, the request runs on a clean stack, and nothing is lost but the trees. dotc already has the two expensive halves of that design, immutable trees and a fresh run per request; what is missing is a checkpoint inside the typer, a cancellation that unwinds instead of degrading, four `finally`s, and a token that reaches the driver.

The obligations of the design are stated and checked on the kernel model ([`ToyKernel`](../../scala-types/ScalaTypes/ToyKernel.lean), §11 of the main note): with no cleanup, abort breaks exactly at the consumed maps and the synthesis burst ([`abort_after_not_resumable`](../../scala-types/ScalaTypes/ToyKernel.lean#L743)); a top-level restore of the unit-scope state repairs those and loses the diagnostics completers emitted, since the facts are memoized and never re-emit them ([`abort_restore_loses_diagnostics`](../../scala-types/ScalaTypes/ToyKernel.lean#L751)); keeping the diagnostics with the facts closes the last gap ([`abort_restore_keep_safe`](../../scala-types/ScalaTypes/ToyKernel.lean#L759)); and idempotent synthetics make abort safe with no cleanup at all ([`abort_proposed_safe`](../../scala-types/ScalaTypes/ToyKernel.lean#L737)). For dotc the last point is moot (a cancelled run is discarded whole), the diagnostics point is moot for the file's own symbols (re-entered by the next run) and real for classpath symbols completed mid-request, and the first point names the two `finally`s that matter: `Touched` and `SymbolLoader`'s `markAbsent`.

## 1. What dotc and Metals do today

From the survey of scala/scala3 at `d168df2a76` and mtags-shared 1.6.9 ([track-i.md §2](track-i.md)), with the facts the spike relies on:

| where | what | consequence |
|---|---|---|
| `InteractiveDriver.scala:48-49` | `myProgressCallback`: `isCancelled() = Thread.interrupted()`, `cancel()` the default no-op | `Run.Progress.checkCancellation` (`Run.scala:719-721`) calls `Thread.interrupted()` itself first; the flag is consumed and `isCancelled()` returns false: cancellation is never sticky |
| `Scala3CompilerWrapper.scala` | `presentationCompilerThread = None` | mtags' `CompilerAccess.withInterruptableCompiler` interrupts only a `Some(thread)`: no interrupt is ever sent |
| `Typer.scala:4147-4159` | `typed` reads `ctx.run.nn.isCancelled` and returns `tree.withType(WildcardType)`, continuing | the only in-typer check degrades instead of unwinding; its writer is the import-suggestion timer (`ImportSuggestions.scala:198-224`), off in the PC (`-Ximport-suggestion-timeout 0`) |
| `Phases.scala:536-544`, `TyperPhase.scala:43-53` | `monitor` checks once per unit and subphase | for a one-file run, nowhere useful |
| `SymDenotations.scala:171-176` | `completeFrom` sets `Touched`, no `try/finally` | an unwind leaves the symbol a `CyclicReference` for the rest of the run; classpath denotations persist across runs in the shared `ContextBase` |
| `SymbolLoaders.scala:451-465` | the `finally` runs `postProcess` → `markAbsent()` on an incomplete root | an unwind through a loader makes the class permanently absent; reachable from the typer through `SourcefileLoader` → `lateCompile` |
| `Annotations.scala:233-235, 251-253` | `LazyAnnotation` sets `myTree = null` before evaluating | an unwind leaves `assert(myTree != null)` to fail later |
| `InteractiveDriver.scala:82-112` | `myCtx` switched before `compileSources`, restored only on `FatalError` | on any other throw the driver points at the partial run, with `myCompilationUnits` stale and `CachingDriver`'s `lastCompiledURI` not updated |
| `Completion.scala:585-586`, `pc/completions/Completions.scala:837` | `catch case error =>`, `catch case _ =>` | would swallow a control exception into a fallback answer |
| mtags `CompilerAccess.withSharedCompiler` | `InterruptException()` → default answer, driver kept; any other `Throwable` → `shutdownCurrentCompiler()` | the cancellation must be, or carry as cause, a `CancellationException`, or the driver is thrown away |

## 2. The design: abort and restart

A request that arrives while a run is typing sets a sticky flag on the driver's progress callback. `Typer.typed` checks the flag every N trees and throws `CancelledCompilation`, a `ControlThrowable` whose cause is a `CancellationException`. The exception passes through every `catch` (the two catch-alls become `NonFatal`), through `completeFrom`, the loaders and the lazy annotations (each restoring what it set), out of `compileSources`, through `InteractiveDriver.run` (which restores `myCtx` and the opened file) and `CachingDriver.run` (which does not count the run as compiled), to `CompilerAccess.withSharedCompiler`, which answers the default and keeps the driver. The next request is a fresh run as before.

**What survives an abort, by kind of state** (the obligations of [track-i.md §11](track-i.md), as dotc has them):

* *Facts.* Denotations are written on completion only; after `Touched` is reset on unwind, an aborted completion is simply re-run by the next request. For the file's own symbols that happens anyway (`unlinkFromFile`, and `Namer.Completer` of an older run → `UnspecifiedErrorType`); for classpath symbols it is the whole point of the `finally`.
* *Trees.* Immutable; the partial `tpdTree` of the aborted run is garbage. Nothing to clear (the one thing scalac has to do per frame).
* *Unit-scope state.* Per `Run`: the aborted run is dropped whole. This is the top-level restore of the model's `Mode.restore`, free.
* *Diagnostics.* Per run (the reporter is the run's); the next run regenerates them because it re-enters and re-completes the file's symbols. The model's [`abort_restore_loses_diagnostics`](../../scala-types/ScalaTypes/ToyKernel.lean#L751) is about a kernel that keeps facts across the abort; dotc keeps only classpath facts, whose diagnostics are not reported to the user. Moot, unless a future targeting mode keeps the file's facts across requests (§5).
* *Global state outside the symbol table.* `recursiveDepth`, `comparersInUse`, `underlyingRecursions` already use `finally`; `trace`'s indent does not (only with tracing on).

**The one thing not to do:** reuse `Run.isCancelled`. It degrades (`WildcardType`) instead of unwinding, and a completion that runs during that window can store a wildcard-derived info in a classpath denotation that outlives the run. The model's name for this is a cache written from a `catch`.

## 3. The change list

Minimal, with the file and the size, from the survey; the spike (§6) implements it.

1. `CancelledCompilation extends ControlThrowable` with `getCause = CancellationException` (so mtags' `InterruptException` matches), ~5 lines.
2. `Typer.typed`: a tick counter on `Run`, `canProgress()` every 1024 trees, throw, ~5 lines. Keep the `isCancelled → WildcardType` branch untouched.
3. `InteractiveDriver`: a `@volatile` cancelled flag, `cancel()` sets it, `isCancelled()` reads it and an installed per-request checker, no `Thread.interrupted()`; `withCancelChecker` installs the checker in `try/finally`, ~10 lines.
4. `completeFrom`: catch `CancelledCompilation`, reset `Touched` if not completed, rethrow (both branches), ~6 lines. `LazyAnnotation`/`LazyBodyAnnotation`: restore the thunk on that exception, ~4 lines each. `SymbolLoaders`: skip `markAbsent` on that exception, ~4 lines.
5. `InteractiveDriver.run`: on `CancelledCompilation` restore `myCtx` and `myOpenedFiles(uri)`, do not `close`, rethrow, ~6 lines. `CachingDriver.run`: a cancelled run is not "already compiled".
6. The two catch-alls → `NonFatal`, 2 lines.
7. `ScalaPresentationCompiler`: wrap the interruptable thunks with `driver.withCancelChecker` fed by `params.token().onCancel().thenAccept(...)` into an `AtomicBoolean`, ~10 lines. (`CancelToken` has no cheap `isCancelled`; `checkCanceled()` throws.)
8. A test: a token cancelled shortly after submission on a large file; the request answers the default, the driver is not recreated (`currentCtx.runId` grows by exactly one on the next request), the next completion on the file is whole; `CompletionCancelSuite` still passes.

## 4. The alternatives, and what the model says about them

* **Nested servicing with taint** (IntelliJ's rule; [track-i.md §7](track-i.md), [`forceT_agree`](../../query/Query/Interrupt.lean#L668)): service inside the run, answer "unknown" for a `Touched` symbol, cache nothing above it. Sound over facts; needs every non-fact mutation to be read-only when tainted, which in dotc means the namer's scope entries and the run's reporter. More latency than abort for a request that needs facts in progress; not for a first step.
* **Per-check state** (the shape of the scalac patch on [retronym/jvm-lang-models#12](https://github.com/retronym/jvm-lang-models/issues/12)): dotc has it already, per run. Abort is per-check state with the check thrown away.
* **Keep interrupting** (`presentationCompilerThread = Some(...)`): the interrupt bit is unsticky and consumed, `ClosedByInterruptException` in a loader becomes `InterruptedException` with `markAbsent` in the `finally`, and `InterruptedException` is a checked `Exception` that the catch-alls swallow. Every reason the survey found for "cancellation never arrives" is a reason not to build on interrupts.

## 5. Targeting, the second phase

With abort in place, the cost of a request is the time to type the file up to the point the request needs. Targeting stops there: `typedStats` (`Typer.scala:4167-4241`) types statements in order, so a check that unwinds once the statement containing the target span is typed is a few lines in `traverse`. Two interactions to design, both about facts that outlive the run: `cleanup` turns every still-lazy symbol of the typed tree into `UnspecifiedErrorType` so no completer captures a dead run's context, which a targeted run would do to most members; and a targeted run's answers for members after the target are the namer's, the gap the space found on scalac (I5, [track-i.md §10](track-i.md)). The model's tree layer (§6 of the main note) is where this gets its theorems; the spike stays on cancellation.

## 6. The spike

A scratch worktree of scala3 at `d168df2a76`, the change list above, and the test of item 8. Status and transcripts are kept on the project board and will be summarised here when the run completes.

## Future work

- [ ] Spike results: the patch, the test's output, the build time; the `Touched` leak reproduced on a classpath symbol if a test can land the cancellation inside its completion.
- [ ] Targeting (§5) as a second patch, with the tree model behind it.
- [ ] The dotc kernel in Lean with abort, so that `abort_*` have dotc-shaped twins (facts dropped per run, diagnostics per run).
- [ ] Upstream: a scala/scala3 issue for "cancellation never reaches the compiler" with the two mechanisms, and the patch as a PR once Metals' side (the token into the driver) is agreed with the Metals maintainers.
