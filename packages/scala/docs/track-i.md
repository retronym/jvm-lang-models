# Track I — Interruptibility: a presentation compiler over lazy facts

21 October 2026. Builds on [Track L](track-l.md): the symbol table as a lazy evaluator.

## Summary for a busy reader

A presentation compiler answers requests while it is in the middle of type checking. "Interrupt" covers two different things: **abort** (the work in progress is thrown away and restarted: scalac's `FreshRunReq` and `CancelException`, IntelliJ's `ProcessCanceledException`) and **nested servicing** (the request runs *inside* the type check in progress, on the same thread, against the same symbol table: scalac's `signalDone` → `pollForWork`). The property wanted is weaker than thread safety, since nothing runs at the same time, but it is not implied by it: a lock lets a nested request straight in (reentrant) or deadlocks (not), so locking does not help. It is the discipline of async-signal safety: every invariant over mutable state has to hold at every safepoint.

Over the lazy facts of Track L the property is free. Every intermediate store of `force` agrees with the semantics ([`force_ok`](../../query/Query/Lazy.lean#L111): `Agree ρ` and `Ext` hold at each step), so a prefix of a forcing leaves a store that is right as far as it goes; abandoning it and restarting gives the same answers, and a nested request serviced with an empty stack is a reordering of demands ([`forceAll_ok`](../../query/Query/Lazy.lean#L160)). The bugs are where a compiler leaves that discipline. [scala/scala#11328](https://github.com/scala/scala/pull/11328) (open, the fix for the flaky presentation tests of [scala-dev#840](https://github.com/scala/scala-dev/issues/840) and [#915](https://github.com/scala/scala-dev/issues/915)) is five of them, one of each kind of non-fact state:

| [scala/scala#11328](https://github.com/scala/scala/pull/11328) commit | the state that is not a fact | the invariant it broke at a safepoint |
|---|---|---|
| `uninterruptible(addSyntheticMethods)` | a class's member set, grown in a burst with safepoints between | `addSyntheticMethods` is all-or-nothing ("already has … not adding"): a nested retype saw part of the burst and skipped the rest |
| `uninterruptible(addSynthetics)`, `consumeSynthetic` | `unit.synthetics`, a per-run map **consumed** when a tree is added | a nested full type check took the remaining trees; a targeted check consumed them and was abandoned |
| keep the implicit factory | the factory symbol's **identity**, replaced each time the template was typed | the run's implicit cache held the replaced symbol, now "shadowed" |
| suspend a targeted check's warnings | `suppressionsKnown`, a **completeness claim** about the unit's `@nowarn`s | a targeted check that stopped early made the claim |
| `CommentPreservingTypers` | a **derived cache** (`cookedDocComments`) whose source (`DocDef`s) typing destroys | cleared per run, not per source |

Three architectures take three positions on this. **scalac** services requests nested, and pays with a safepoint invariant over all of the above. **dotc under Metals** never interrupts: a request is a fresh `Run` of its file on a shared symbol table, requests wait in a one-thread LIFO queue, a running job is not interrupted (there is no presentation compiler thread, and an interrupt bit is swallowed at the checkpoints), and any exception throws the driver away; it pays with whole-unit recompilation. **IntelliJ's PSI** aborts only: a read action is cancelled at its next `checkCanceled` by a write action, and restarted; everything but the parse is a pure function cached under a modification count, computed by whoever asks first, with a recursion guard that answers `null` on re-entry and forbids caching above the re-entered frame; it pays with the design constraint that read actions write nothing but caches.

[`probes/interrupt`](../probes/interrupt) is the three architectures distilled into one Java program (about 1,100 lines) over a toy language of classes and members without expressions, and a harness that injects one request at every safepoint of the background work and compares the answers with the request arriving after it. Under the scalac kernel with the policy before [scala/scala#11328](https://github.com/scala/scala/pull/11328), the four scenarios modelled on the PR's tests diverge at 8–13 of 14–18 safepoints; with the PR's policy, at none. The dotc and PSI kernels diverge at none, in every scenario, by construction. The toy also predicts two behaviours of scalac *after* the PR, for a request that types the whole unit (`askType(source)`) served inside the background check of that unit ([results.txt](../probes/interrupt/results.txt), `case-class-loaded`): served before the class is typed, the background's final tree, which later `askLoadedTyped`s return, has none of its synthetics; served after, the request's own tree has none. Both are testable with the PR's own `signalDone` hook, and are findings I1 and I2.

## 1. What [scala/scala#11328](https://github.com/scala/scala/pull/11328) is about

scalac's interactive `Global` runs one compiler thread. `backgroundCompile` types the loaded units; the typer calls `signalDone` after every tree it types, and there, if `interruptsEnabled && lockedCount == 0 && !context.bufferErrors`, `checkForMoreWork` services the requests that have arrived, *inside* the type check in progress. A targeted request (`askTypeAt`, `askTypeCompletion`) types the unit until the tree containing the target position is typed and unwinds with `TyperResult`; `askType(source)` types the whole unit nested; `askReload` starts a new run and unwinds the background check with `FreshRunReq`. The three guards cover the facts: no completer is in progress (`lockedCount`), no speculative typing is in flight (`bufferErrors`), and no region has asked to be left alone (`interruptsEnabled`, which the PR makes settable from the typer).

Everything [scala/scala#11328](https://github.com/scala/scala/pull/11328) fixes is state outside the facts, listed in the summary. The PR's two new tests are the shape of the harness below: a `signalDone` override that blocks the compiler thread at the first serviceable safepoint until a completion has been posted, then an `askLoadedTyped` whose tree is compared with the expected one. Jason's review comment asks for the generalisation: a soak test that interrupts with random interleavings. [`Harness.java`](../probes/interrupt/src/pctoy/Harness.java) is that, exhaustively, over the toy.

## 2. Three architectures

### scalac (`src/interactive`)

* Where a request runs: nested, at `signalDone` (`Global.scala:337`), through `pollForWork`.
* Symbol table: one, shared across runs. A new run re-enters a reloaded unit's definitions with `enterExistingSym`, which keeps the symbols and resets their infos to completers, so references from other units stay valid by identity.
* The black hole: `LOCKED`, set in `completeInfo` and reset in its `finally` (`Symbols.scala:1559-1600`), so an abort through a completer leaves the symbol forceable; a cycle gives the asked symbol `ErrorType` for the run.
* Cancellation: `CancelException` and `FreshRunReq` unwind to the run loop; `TyperResult` unwinds a targeted check.

### dotc (`compiler/src/dotty/tools/dotc/interactive`) under Metals (`presentation-compiler`, mtags-shared's `CompilerAccess`)

Read for this track in scala3 at `d168df2a76` and mtags-shared 1.6.9; the survey's details are in the agent report summarised here.

* Where a request runs: `InteractiveDriver.run(uri, source)` makes a fresh `Run` from `myInitCtx` for every request, sharing the `ContextBase` (symbol table, phases) across runs (`InteractiveDriver.scala:81-107`). `CachingDriver` skips the run when the URI is the last compiled and the text unchanged. There is no targeted type check: the whole unit is typed, and completions and hovers are read off the typed tree afterwards.
* Symbol table: shared. A run of a file unlinks the file's symbols from earlier runs when the package symbol is created (`unlinkFromFile`, `SymDenotations.scala:2792`); references to them from other facts are stale denotations, and in `Mode.Interactive` (`Config.ignoreStaleInIDE`) `bringForward` accepts them and resolves by name to the current symbol. A completer created in an older run does not run: the symbol gets `UnspecifiedErrorType` (`Namer.scala:933`). After a run, `cleanup` gives every symbol in the typed tree whose info is still lazy an error type, so no completer captures an old run's context.
* The black hole: `Touched`, set in `completeFrom` (`SymDenotations.scala:150-176`) and **not** reset if the completer throws; `isCompleting` then stays true and the next access is a `CyclicReference`. `LazyAnnotation` leaves `myTree = null` the same way. `BaseData` does use `try/finally`.
* Cancellation: the compiler checks `Thread.interrupted()` only at unit and subphase boundaries (`Run.checkCancellation`, `Phases.monitor`); nothing inside typer, completion or implicit search checks (the separate `Run.isCancelled` flag is the import-suggestion timeout). With `InteractiveDriver`'s callback (`isCancelled() = Thread.interrupted()`, `cancel()` a no-op) a pending interrupt is cleared by the first `Thread.interrupted()` and the checkpoint reports "not cancelled". And Metals never sends one: `Scala3CompilerWrapper.presentationCompilerThread` is `None`, and `CompilerAccess.withInterruptableCompiler` interrupts only when there is a thread. Requests go through `CompilerJobQueue`, a one-thread executor over a LIFO queue; a cancelled token drops a job that has not started (`result.cancel(false)`), a timeout resets the queue and discards the compiler while the old job keeps running on the old driver; `withSharedCompiler` maps `InterruptException` to the default answer and keeps the driver, and any other `Throwable` to `shutdownCurrentCompiler`, so the next request builds a new driver with a new `ContextBase`.

So dotc is interruptible by not being interrupted: a request is an idempotent unit of work at the granularity of a file, and the only recovery is to throw the driver away. The hypothetical kernel `dotc-interrupted` below asks what would happen if an interrupt did land mid-run and the driver were kept, as `withSharedCompiler` does for an `InterruptException`.

### IntelliJ PSI (platform `RecursionManager`, `CachedValuesManager`; the Scala plugin's `caches` package)

* Where a request runs: on its own thread as a read action, concurrently with the daemon's. No request is ever serviced inside another computation.
* Symbol table: none. Declarations are stubs, available from the parse without any computation (level 0 of Track L §3). Everything else (`members`, a member's type, the implicit candidates) is a pure function of the stubs, cached per element under a modification count (`CachedValue`; the plugin's `Cache0`/`CacheN` compare a `modCount` and `compareAndSet` the value, under `ModTracker.anyScalaPsiChange` or a `BlockModificationTracker` for edits inside a body). Identity across edits is a `SmartPsiElementPointer`, which re-resolves.
* The black hole: `RecursionManager.doPreventingRecursion(key, memoize, computation)` returns `null` on re-entry (`RecursionManager.java:95-103`) and marks every frame above the re-entered one, so `StackStamp.mayCacheNow()` is false there and the value is not cached (`CacheInUserData.scala:32`, `Cache0.scala:32`). A result that depended on what was on the stack never reaches the store: the exact cure for Track L's peeking consumer ([`forcePeek`](../../query/Query/Lazy.lean#L249)), whose order-dependent answer scalac memoizes.
* Cancellation: a pending write action makes every read action's next `ProgressManager.checkCanceled()` throw `ProcessCanceledException`; the reader unwinds without publishing (a `CachedValue` is stored only on return) and is restarted (`ReadAction.nonBlocking`).

The difference in one line: scalac buys latency by running other requests inside the current one and pays with a safepoint invariant over all mutable state; PSI buys it by abort-and-restart and pays with the separation of reads from writes and caches that are pure; dotc under Metals buys simplicity by neither interrupting nor nesting, and pays in recomputation.

## 3. The toy

[`probes/interrupt/src/pctoy`](../probes/interrupt/src/pctoy), plain Java 21, `run.sh` compiles and runs it.

**The language** ([`Ast.java`](../probes/interrupt/src/pctoy/Ast.java)): a file is classes, objects and traits with members and no expressions. A member's type is declared (`def m: T`) or inferred from a path (`def m = a.b.c`): the first name is a member of the enclosing class or a top-level object, each further name a member of the type so far, or, failing that, of an implicit class in scope that takes that type. Inference is what forces other facts, so this is enough for cycles (`def a = b; def b = a`), levels (a class's members are entered before any member's type is asked), synthetics with the structure of scalac's (a `case` class gets `copy`, `equals`, `hashCode`, `toString` in a burst and a companion with `apply` and `unapply` through `unit.synthetics`; an `implicit` class gets a factory method), implicit search with a per-run cache and a shadowing check, and warnings with `@nowarn` suppression (`deprecated def`, `nowarn object`).

**The shared symbol table** ([`Global.java`](../probes/interrupt/src/pctoy/Global.java)): symbols with completers, `force` with the black hole, a namer per run, a typer that calls `signalDone` after each member, each synthetic and each class, as well as inside a completer (where `lockedCount > 0` and scalac would not service). `Policy` holds six booleans: the four choices the PR changed (an uninterruptible synthesis burst, synthetics kept for a targeted check with scalac's `SynthesizedMethods` attachment, the factory symbol kept, a targeted check's warnings left suspended), `unlockOnUnwind` (scalac true, dotc false) and `reuseSymbols` (scalac's `enterExistingSym` true, dotc's `unlinkFromFile` false, with stale symbols re-resolved by name).

**Five kernels**, each a `Kernel` ([`Core.java`](../probes/interrupt/src/pctoy/Core.java)) with `reload`, `send(event)` and `drain()`:

| kernel | where a request runs | model of |
|---|---|---|
| `scalac-before`, `scalac-after` ([`Scala2Kernel`](../probes/interrupt/src/pctoy/Scala2Kernel.java)) | nested at `signalDone` when `interruptsEnabled && lockedCount == 0`; a targeted check unwinds with `TyperResult`; an edit is a new run and `FreshRunReq` | scalac before and after [scala/scala#11328](https://github.com/scala/scala/pull/11328)'s four policy changes |
| `dotc-metals` ([`Scala3Kernel`](../probes/interrupt/src/pctoy/Scala3Kernel.java)) | a fresh run of the file per request, whole unit, LIFO queue, never interrupted, `CachingDriver`'s skip, `cleanup` | dotc under Metals |
| `dotc-interrupted` | as above, but the interrupt is delivered once at the next checkpoint of the job it arrived in, the job unwinds, and the driver is kept | the hypothetical `InterruptException => default` path |
| `psi` ([`PsiKernel`](../probes/interrupt/src/pctoy/PsiKernel.java)) | stubs by name; `cached(key)` under a modification count with a recursion guard that answers `null` and taints the frames above; a request is a read action on a fresh guard stack; an edit is a write action that cancels the daemon at its next `checkCanceled` | IntelliJ PSI as the Scala plugin uses it |

**The harness** ([`Harness.java`](../probes/interrupt/src/pctoy/Harness.java)): a scenario is sources and one event, a request (`completion F Decl.member`: the members of the target member's type, implicit views marked `via`; `loadedTyped F`: every declaration's typed body and the problems reported, scalac's `askType(source)`) or an edit followed by a request. The background's safepoints are counted on a fresh kernel; the reference answers come from a fresh kernel with the event sent after the background finishes, followed by a `loadedTyped` of each file; then, for each safepoint `k`, a fresh kernel gets the event injected at `k`, and its answers (the event's, then the final `loadedTyped`s) are compared with the reference. "Work" counts completers run and members typed, so the price of each design shows beside its correctness.

## 4. Results

[`results.txt`](../probes/interrupt/results.txt), from `run.sh`. Divergent safepoints out of the background's total, and work (reference / mean over the interleavings):

| scenario (the PR's test it mirrors) | scalac-before | scalac-after | dotc-metals | dotc-interrupted | psi |
|---|---|---|---|---|---|
| `case-class-completion` (dollar-completion, scala-dev#915) | 8/16 | 0/16 | 0/16 | 0/16 | 0/19 |
| `case-class-loaded` (nested `askType` while apply/unapply are added) | 16/16 | **16/16** | 0/16 | 0/16 | 0/19 |
| `targeted-consumes-synthetics` (local-case-class-interleaved) | 9/18 | 0/18 | 0/18 | 0/18 | 0/20 |
| `implicit-class` (implicit-class-interleaved) | 10/17 | 0/17 | 0/17 | 0/17 | 0/16 |
| `nowarn` (t12308, scala-dev#840) | 13/14 | 0/14 | 0/14 | 0/14 | 0/14 |
| `cycle` (a true cycle beside a well-founded reference) | 0/12 | 0/12 | 0/12 | 0/12 | 0/13 |
| `edit-cross-file` (an edit of `B` while `A`, which reads `B`, is typed) | 0/11 | 0/11 | 0/11 | **5/11** | 0/11 |
| work, `implicit-class` | 17 / 22.0 | 17 / 21.8 | 17 / 17.0 | 17 / 26.7 | 11 / 11.2 |

What the table says:

* **The PR's four fixes close the four shapes they target**, and the toy reproduces each with the mechanism the commit messages describe: the partial burst and the all-or-nothing skip, the consumed map, the replaced symbol in the cache, the premature completeness claim. In `implicit-class` the divergent safepoints are 0–6 and 14–16: a completion served while `Before` is typed (the factory replaced after the cache is filled) or after `Use.g` is typed (the cache filled, then the factory replaced by the next retype).
* **A nested full type check is still unsafe after the PR** (`case-class-loaded`, finding I1/I2). Served at a safepoint before the background has typed the case class, the nested check consumes the synthetics and the background's own tree, which it stores last, lacks the companion, `apply`, `unapply` and, by the all-or-nothing skip, `copy`..`toString`; served after, the request's own tree lacks them all. The PR closes only the window inside `addSynthetics`. The mechanism in scalac is `typeCheck(unit)` (`Global.scala:675`): the outer `typer.typed(unit.body)` took the old body as its argument and assigns `unit.body` when it returns, after the nested one; `typed` short-circuits only trees that carry a type, and the old `ClassDef` does not. This is a prediction from the toy, to be checked with a test in the shape of the PR's.
* **dotc under Metals never diverges**, and does no extra work for a request that arrives during the background compile, because the request waits. The reference work equals the mean: the design has no interleavings. Its cost is elsewhere, in a whole-unit run per edit, which the toy's one-file scenarios do not weigh.
* **An interrupt delivered to dotc would be mostly harmless, and the cache keyed on the last file is the hazard.** `dotc-interrupted` recomputes (mean work 26.7 against 17.0) and diverges only in `edit-cross-file`, at the safepoints inside `B`'s initial compile: the abandoned run leaves `CachingDriver`'s "last compiled" at `A`, so the request after the edit answers from `A`'s compilation against the state before `B` existed. The `Touched` leak does not show in these scenarios, because `cleanup` and the fresh run per file leave no cross-file completer to be interrupted; it would need a symbol loader, which has its own `finally`.
* **PSI never diverges and does the least work**: the completion after the background costs nothing, an interleaved one computes only what it needs, and the daemon re-annotates only after a change. The recursion guard gives the true cycle the same error in every interleaving, as scalac's `LOCKED` with `ErrorType` does; the two differ for a *peeking* consumer (Track L §6), which the toy does not yet have.

## 5. The theory, and what the next model should say

The nested-servicing bugs are all outside `Query.Lazy`'s store, so the formal step is to add what they are over:

1. **Abort safety is a corollary.** For `force`: any prefix of a forcing leaves a store satisfying `Agree ρ` and `Ext`; restarting from it gives the same answers. This is [`force_ok`](../../query/Query/Lazy.lean#L111)'s induction read as a statement about intermediate states, plus `unlockOnUnwind` (an aborted frame must leave the stack): scalac's `finally unlock()` satisfies it, dotc's `completeFrom` does not, and an aborted dotc frame is a permanent black hole for the run.
2. **Nested servicing is a reordering when the stack is empty** ([`forceAll_ok`](../../query/Query/Lazy.lean#L160)), and with a non-empty stack it is either a spurious black hole or, under peek semantics, an order-dependent answer that gets memoized. PSI's taint is the fix: a peeked answer is not stored, so the store still agrees with `ρ`. `forcePeek` with a taint flag, and the theorem that the store stays `Agree`.
3. **The non-fact state of [scala/scala#11328](https://github.com/scala/scala/pull/11328)**: a pushed fact read in the middle of its burst is `Query.Freeze` without the freeze; "uninterruptible" is the burst having no safepoint. A consumed map is a linear resource: a request that consumes and is then abandoned, or that consumes what the outer computation will look for, breaks the invariant that each synthetic is added once to the tree that is kept. An identity cache (the implicit cache) is sound only if the symbol it names is stable within the run. A completeness claim (`suppressionsKnown`) is a freeze made by a computation that did not finish.

## Future work

- [ ] Run the two predictions (I1, I2) against scala/scala at the PR's branch with a test in the shape of `local-case-class-interleaved` and an `askType` served nested; then the soak test proper: random interleavings over `test/files/presentation`.
- [ ] A peeking consumer in the toy (scalac's implicit search skipping a `LOCKED` candidate), so the psi and scalac kernels differ on a cycle that is avoided rather than reported.
- [ ] Edits inside a member (a `BlockModificationTracker` edit) so that PSI's invalidation granularity, and dotc's whole-unit rerun, show in the work column.
- [ ] The Lean statements of §5 over `Query.Lazy`: abort safety, nested servicing as reordering, peek with taint, and the three kinds of non-fact state.
