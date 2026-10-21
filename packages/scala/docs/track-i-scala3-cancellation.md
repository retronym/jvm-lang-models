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

## 4a. Prior art and positions

Researched 22 October (issues, PRs and sources of scalameta/metals and scala/scala3). The design above is the missing half of work the maintainers have already started, and it has to answer one stated position.

* **Cancellation was removed for Scala 3 on purpose, for I/O reasons.** [scalameta/metals#4200](https://github.com/scalameta/metals/pull/4200) (tgodzik, 2022): "Don't use interrupt for the Scala 3 compiler", fixing [#4196](https://github.com/scalameta/metals/issues/4196): a thread interrupt landed in `jdk.nio.zipfs` and closed the classpath jar's channel for good (`ClosedByInterruptException`, then `ClosedChannelException` on every later read). That is why `presentationCompilerThread` is `None`. The harm documented is to NIO channels, not to the typer's state; a sticky flag polled at a checkpoint never touches the interrupt bit, so it avoids the whole failure.
* **The hook exists and was built for this.** [scala/scala3#18739](https://github.com/scala/scala3/pull/18739) (bishabosha, 3.4.0) added `ProgressCallback`, `Run.Progress` and `checkCancellation` with "cooperative interruption of compilation (e.g. cancellation from within an editor)" as a stated goal. [scala/scala3#24133](https://github.com/scala/scala3/pull/24133) (rochala, 3.8.0) installs a callback in `InteractiveDriver` (`isCancelled() = Thread.interrupted()`) with "future changes are required to make it work with safe `ScalaPresentationCompiler` and `CancelTokens`". As §1 shows, that callback is never sticky: `checkCancellation` consumes the interrupt bit before asking it. The spike's test is the first to exercise it.
* **The direct prior attempt found what the model predicts.** [scala/scala3#23191](https://github.com/scala/scala3/pull/23191) (rochala, draft 2025, closed 2026 unmerged, superseded by `RawPresentationCompiler`): a job queue whose `ProgressCallback.isCancelled` read the token, "this makes all requests way faster as we will be able to cancel during type-checking", and the finding that "`ProgressCallback.isCancelled = true` throws random errors in the compiler", so the errors were wrapped into a `CancellationException`. The flag path exits gracefully (`Typer.typed` returns `WildcardType`, `typedImplicit` fails) and the run goes on with garbage: the "cache written from a catch" of §2, observed. kasiaMarek approved; nobody objected to cancelling inside the typer.
* **The position to answer.** [scala/scala3#9429](https://github.com/scala/scala3/pull/9429) (2020), odersky: "the idea of `Run#isCancelled` is that it provides a way to exit gracefully, without throwing exceptions"; smarter wanted the interrupt bit checked and a `Reporter.cancelled`-style result. `Run.isCancelled` was born as a *budget* for import suggestions ([#7862](https://github.com/scala/scala3/pull/7862), [#9167](https://github.com/scala/scala3/pull/9167), `-Ximport-suggestion-timeout`), where a partial result is wanted. A presentation-compiler request never wants the partial result, and #23191 shows what the graceful path leaves behind; unwinding with a control exception and resetting `Touched` is what makes the driver reusable. That is the argument, with the model's theorems and #23191's "random errors" as the evidence.
* **No targeted typing exists for the Scala 3 PC**, and nobody has proposed it: [scalameta/metals#4225](https://github.com/scalameta/metals/pull/4225) / [scala/scala3#17715](https://github.com/scala/scala3/issues/17715) (2022) established that every request retypes the whole unit (fixed only by a content-hash cache, `CachingDriver`); [scala/scala3#19589](https://github.com/scala/scala3/pull/19589) (outline typing) is batch-oriented. Cancellation is therefore the only latency lever today, and targeting (§5) is open ground.
* **Where the checkpoint must reach.** [scala/scala3#19320](https://github.com/scala/scala3/issues/19320): one missing implicit made a request run for minutes inside implicit search, so the tick has to be observed inside `searchImplicit`'s loops too, not only in `typed`. [scalameta/metals#8881](https://github.com/scalameta/metals/issues/8881): 2–3 s per keystroke on a 4,600-line file, requests serialised behind each other, so abort latency compounds.
* **The fallback is itself a problem.** The 20 s timeout orphans the running job (`CompilerJobQueue.reset` is `shutdown`, not `shutdownNow`) and builds a new compiler; [scalameta/metals#8883](https://github.com/scalameta/metals/pull/8883) and [#8915](https://github.com/scalameta/metals/pull/8915) (2026) fixed leaks in that restart path. rochala's closing view on #23191: runaway compilations belong in a separate JVM. A design that keeps the driver and unwinds is cheaper than every restart.
* **Elsewhere.** rust-analyzer cancels by unwinding (a panic with a special value, caught at the `ide` boundary) and documents that a cancelled query must not poison the revision; the Kotlin K2 Analysis API's recurring bug class is a swallowed `ProcessCanceledException` (KT-50253, KT-71942); IntelliJ's Scala plugin has 91 `checkCanceled` sites inside type computation. The `catch` audit of §3 is the same lesson three times.

## 5. Targeting, the second phase

With abort in place, the cost of a request is the time to type the file up to the point the request needs. Targeting stops there: `typedStats` (`Typer.scala:4167-4241`) types statements in order, so a check that unwinds once the statement containing the target span is typed is a few lines in `traverse`. Two interactions to design, both about facts that outlive the run: `cleanup` turns every still-lazy symbol of the typed tree into `UnspecifiedErrorType` so no completer captures a dead run's context, which a targeted run would do to most members; and a targeted run's answers for members after the target are the namer's, the gap the space found on scalac (I5, [track-i.md §10](track-i.md)). The model's tree layer (§6 of the main note) is where this gets its theorems; the spike stays on cancellation.

## 6. The spike

A scratch worktree of scala3 at `d168df2a76`, the change list of §3 as [`dotc-cancellation.patch`](../../../docs/upstream/dotc-cancellation.patch) (12 files, +344/−12), and a new `CompletionAbortSuite` (three tests). A full rebuild of the bootstrapped compiler took two minutes, test iterations 7–20 s. **All three suites pass**, `CompletionCancelSuite` and `CompilerCachingSuite` included:

```
[abort-inside-completion] thrown=true polls=1
[abort-inside-completion] completion after abort: greetAlpha: Any
[abort-from-typer] thrown=true typerPolls=2 runId 5 -> 5
[abort-from-typer] runId after following request: 7
[abort-via-token] runId before cancelled request: 7
[abort-via-token] runId after cancelled request: 7
[abort-via-token] runId after following request: 9
[info] Passed: Total 11, Failed 0, Errors 0, Passed 11
```

What the tests pin down. `abort-via-token`, end to end through Metals' `CompilerAccess`: a token that cancels 20 ms after submission on a 400-method object; the request answers with `InterruptException()`, the driver is the same object before and after (`runId` 7 → 7, not recreated), and the next completion on the file is whole (`runId` 9: the aborted run consumed one id, so +2, where a recreated driver would restart at 2). `abort-from-typer`: the checker is driven directly and answers true at the second poll whose stack holds `checkCancelledTyping`, so the abort provably comes from the typer checkpoint; `myCtx`, the opened file and the compilation unit are the previous ones afterwards. `abort-inside-completion-of-sourcepath-symbol`: the cancellation lands inside `completeFrom` of a sourcepath symbol whose body is 2,000 trees (`polls=1`: the first 1,024 trees of the run are inside its Namer completion); after the abort the next completion lists it. **The control run** with `untouchIfIncomplete` made a no-op: the same completion comes back empty, because the symbol is a `CyclicReference` for the rest of the run. That is `touched_stays_cyclic` on the real compiler, and the reset is the fix.

What the spike found beyond the change list:

* **A cancellation before the typer drops the unit.** `tryEnterUnit` skips a unit when the callback is already cancelled, and `InteractiveDriver.run` then fails on `ctxRun.suspendedUnits.head`, which mtags would treat as a crash and discard the driver. The patch checks the callback after `compileSources` and throws `CancelledCompilation`; `CompletionCancelSuite.basic` (a token cancelled before the thunk runs) now exercises that path.
* **The throw is guarded by `Mode.Interactive`.** Batch and sbt keep today's behaviour (a cancelled run skips its remaining units); without the guard sbt would get a `ControlThrowable` out of `compileSources`.
* **`Compiler.newRun` resets the `ContextBase`** (uniques, sources, files, comparers) before the run starts, so after an abort the previous run's trees are not servable even with `myCtx` restored: a completion on identical content answered from `CachingDriver`'s cache came back empty. The patch invalidates the cache on a cancelled run (`lastCompiledURI = null`), so the next request recompiles. For the non-caching `InteractiveDriver` the retained `myOpenedTrees`/`myCompilationUnits` have the same staleness; `close(uri)`, what the `FatalError` path does, may be the honest choice. Open.
* **A symbol first touched in a later run than its namer gets `Any`.** The retried completion lists `greetAlpha: Any`, not `Int`: `Namer.Completer.complete` refuses to complete in a run later than its creation run (`denot.info = UnspecifiedErrorType`, asserting `Mode.Interactive`). Pre-existing for any sourcepath member first touched late, and the model's `abort_restore_loses_diagnostics` in another form: a fact dropped on abort and not regenerated. A real fix re-enters the file or re-creates the completer in the next run (finding I7).
* **`LazyAnnotation`'s restore must re-wrap the thunk**: assigning the context function to the union-typed field applies it during unwinding.
* **`getCause` on a `ControlThrowable`** can be overridden (the constructor only pins the `cause` field), so mtags' `InterruptException` matches `CancelledCompilation` with no change on the Metals side; `Scala3CompilerAccess` overrides `withInterruptableCompiler` once to install the checker from `token.onCancel()`, with no per-call-site change in `ScalaPresentationCompiler`.
* **Build note**: the Homebrew `sbt` script appends `-Xmx2G` after `.jvmopts`' 8 GB, and GenBCode ran out of memory once; `sbt --mem 8192`.

## Future work

- [x] Spike: the patch, three tests, the `Touched` leak reproduced on a sourcepath symbol and fixed (§6).
- [ ] The two open questions of §6: `close(uri)` after an abort for the non-caching driver; a symbol first touched after its namer's run (I7).
- [ ] The checkpoint inside implicit search (`searchImplicit`), for [scala/scala3#19320](https://github.com/scala/scala3/issues/19320)'s shape.
- [ ] Targeting (§5) as a second patch, with the tree model behind it.
- [ ] The dotc kernel in Lean with abort, so that `abort_*` have dotc-shaped twins (facts dropped per run, diagnostics per run).
- [ ] Upstream: a scala/scala3 issue that the 3.8.0 `InteractiveDriver` cancellation is never sticky (the interrupt bit is consumed by `checkCancellation`), with the spike's test; then the patch as the "future change" #24133 named, framed against #9429's graceful-exit position with #23191's evidence.
