# I24 and I27: mechanisms, reproductions, candidate fixes

Read-only analysis of the patched worktree (`scala3-cancel`, paths below are relative to `compiler/src/dotty/tools/dotc/` unless said otherwise), `server22.log`, and the Metals log of `~/code/scratch/dotc-session-dotc`. Nothing was run.

Verdicts up front:

- **I24: mechanism established** (by code reading; the assertion message names the states and the code paths fit it exactly). A resume types a skipped statement under the typer state recorded when it was skipped; for a statement inside a closure argument that state is `tryEither`'s nested state, committed when the enclosing application succeeded. The first nested state the resumed typing commits into it fires `TyperState.commit`'s "into already committed" assertion. Latent on the current build, not fixed by I20–I26; I20's block-level resume made it reachable from every closure body.
- **I27: the assertion is established, the state that feeds it is plausible, not proven.** The Metals log holds a *second* occurrence (22:22:19, `SymDenotations.scala`) with a full stack that the finding missed: `assert(ctx.erasedTypes || ctx.reporter.errorsReported)` at `core/TypeOps.scala:247`, reached from `Namer.inferredResultType` widening an inferred union whose alternatives have no common base class, i.e. one alternative is an error-like type that no reported error accompanies. The 21:46 `Parsers.scala` failure is the same bare message on the same request path, and in both cases the next request ran on a *fresh compiler instance* (mtags restarts the PC after a `compiler-error` report; the run ids restart at 3), so the state was accumulated in the instance, not in the file. Which spike change plants the silent error type is the open question; candidates ranked below, with a test that exercises the most likely one.

---

## I24: a resume commits into a committed typer state

### The assertion

`core/TyperState.scala:168-182`:

```scala
  def commit()(using Context): Unit = {
    Stats.record("typerState.commit")
    assert(isCommittable, s"$this is not committable")
    assert(!isCommitted, s"$this is already committed")
    val targetState = ctx.typerState

    val nothingToCommit = (constraint eq targetState.constraint) && !reporter.hasUnreportedMessages
    assert(!targetState.isCommitted || nothingToCommit ||
       // Committing into an already committed TyperState usually doesn't make
       // sense since it means the constraints and messages we're committing won't be propagated
       // further, but it can happen if the targetState gets captured in a reported
       // Message, because forcing that Message might involve creating and
       // committing new TyperStates into the captured one after it's been committed.
        targetState.reporter.hasErrors || targetState.reporter.hasWarnings,
      s"Attempt to commit $this into already committed $targetState")
```

Reading the message `Attempt to commit TS[102456, 102106X, 101854, 101853, 0] into already committed TS[102106X, 101854, 101853, 0]`:

- `toString` (`TyperState.scala:311-315`) prints the chain `id :: previous...`, and the `X` marks `!isCommittable`, not `isCommitted`. `commit()` does `setCommittable(false)` after flushing (line 184), so a committed state prints with `X` too; the assertion that fired is the third one, which tests `targetState.isCommitted`, so 102106 is *committed* (not merely an explore state).
- `targetState` is `ctx.typerState` at the commit: the context the resumed statement is being typed in has typer state 102106, committed.
- `this` = 102456 was created by `ctx.fresh.setNewTyperState()` (`Contexts.scala:713-714`: `typerState.fresh(committable = true)`, whose `previous` is 102106) *during the resumed typing*, and its constraint differs from the target's (`nothingToCommit` false), and the target has no errors or warnings.
- 101854, 101853 are uncommitted, committable ancestors (the unit's state from `TyperPhase.scala:71` → the run's state from `Run.scala:704` `ctx.typerState.fresh(ctx.reporter)`; 0 is the context base's initial state). That is what package- and template-level `typedStats` normally run under: one committable state per unit that nothing ever commits; type variables created at that level are interpolated per definition.

### How the resume reaches it

The log (`server22.log` lines 229-231, requests #196-#198, run 48, build before I20-I26 were fixed):

1. `#196 typeAt@3723 fresh`: a targeted run with the target in `run`'s body; `cleanup` (a template-level `def`) is skipped with `SkippedStat(stat, ctx, dummy)` where `ctx.typerState` is the unit's state (uncommitted).
2. `#197 typeAt@5532 resumed`: target in `t.removeAllAttachments()`, the last expression of the closure `tree.foreachSubTree { t => ... }` inside `cleanupTree`. The resume (`interactive/InteractiveDriver.scala:310-325`) types `cleanup` whole along the path. `tree.foreachSubTree { t => if (...) {...}; t.removeAllAttachments() }` is typed by `Applications.typedApply`, whose normal path is `tryEither(simpleApply(fun1, proto))` (`typer/Applications.scala:1497`); `tryEither` (`typer/Typer.scala:142-153`) creates `nestedCtx = ctx.fresh.setNewTyperState()` = **102106** and runs `simpleApply` under it. `simpleApply` types the closure argument through `ApplyToUntyped.typedArg` → `proto.typedArg(arg, formal)` (`Applications.scala:1287`, `typer/ProtoTypes.scala:544-556`) under the *current* context, i.e. 102106 (not the proto's creation state: that is the plural `typedArgs` path, `ProtoTypes.scala:496-501`). The closure body is a `Block`; `typedBlock` → `typedBlockStats(stats, blockSpan)` (`Typer.scala:1602-1624`) marks it for targeting because the block's span contains 5532, and `typedStats` skips the `if (t.symbol.exists && t.hasType) {...}` statement, recording it at `Typer.scala:4317` as `Run.SkippedStat(stat, ctx, exprOwner, inBlock = true)` with `ctx.typerState eq 102106`. `simpleApply` succeeds, `tryEither` commits 102106 into 101854 (`Typer.scala:151`): 102106 is now `isCommitted`, non-committable, and its type variables (`foreachSubTree`'s `U`) now belong to 101854 and are instantiated there.
3. `#198 typeAt@5419 error`: the target is inside the skipped `if`, so `runUpTo0` finds it with `skippedAt` and calls `resume`, which types it with `ctx0 = sk.ctx` (`InteractiveDriver.scala:316-320`): `typedStats(sk.stat :: Nil, sk.owner)(using ctx0)`, typer state 102106. The statement's body contains `t.symbol.annotations.foreach { annot => ... }` (and `seen(annot.tree)`, `cleanupTree(annot.tree)`): the first polymorphic application goes through `typedApply` → `tryEither` → `nestedCtx.typerState` = **102456** (previous 102106), its constraint gains `foreach`'s `U`, the apply succeeds, `nestedCtx.typerState.commit()` at `Typer.scala:151` finds `ctx.typerState` = 102106 committed → the assertion.

Any other `setNewTyperState` + `commit` pair reachable from a statement does the same: `Typer.tryEither`/`tryAlternatively` (`Typer.scala:142-165`), extension-method selection (`Typer.scala:4590-4622`), `typedFunctionValue`'s expression-body inference (`Typer.scala:2024-2032`), `normalizedCompatible` (`ProtoTypes.scala:67-74`), `Implicits.scala:1219-1228`, `Applications.scala:1788, 1889`. The `nothingToCommit` escape (`constraint eq targetState.constraint`) is why most resumes into closure bodies pass: a statement whose nested attempts create no type variables commits nothing. The assertion needs a resumed statement with a polymorphic application or an implicit search *inside* a `tryEither`-style attempt, and an error-free target. That is also why it has not recurred: it is not fixed, it is rare.

Before the assertion is even reached the resumed typing runs with a stale, frozen constraint: `TypeVar.instanceOpt` and `isInstantiated` read `ctx.typerState.constraint`, and 102106's constraint stops at its commit, so a type variable instantiated later in 101854 (by the enclosing application's interpolation) looks uninstantiated inside the resumed statement. Silent wrong answers are possible on the paths where the assertion does not fire.

### Exposure, and whether the block-level resume widened it

- Before I20, only package- and template-level statements were resumed; their recorded contexts carry the unit's state except for a template typed *inside an expression*, i.e. a class on the path to the target that is an argument: `foo(new Bar { def a = ...; def b = @@ })` records `def a` under `tryEither`'s state (`typedClassDef`, `Typer.scala:3582-3587`, targets a class when `cdef.span.contains(typingTarget)`, whatever the enclosing expression). Rare.
- I20's block-level resume (`typedBlockStats`, `Run.SkippedStat.inBlock`) records a context for every statement of every targeted block, and a block inside a closure argument is the common case (`xs.foreach { x => ...; ... }`, `map`, `tap`, `foreachSubTree`). So yes, the exposure widened from "a class inside an argument" to "any statement of a closure body inside an application". `completeSession` (`InteractiveDriver.scala:125-160`) types every skipped statement under `sk.ctx` the same way and has the same exposure, in bulk.
- A second, sibling failure mode: an argument typed during overload resolution or applicability testing is typed under an *explore* state (`Applications.isApplicableMethodRef` → `explore`, `Contexts.scala:715-716`, committable = false) and cached by `cacheTypedArg` (`ProtoTypes.scala:459-486`) for reuse. A block skipped there records a non-committable state; a resume that creates and commits a nested state under it fails the first assertion, `TS[...] is not committable`.

### Alternatives ruled out

- The resumed typing committing the same nested state twice: that trips `assert(!isCommitted, s"$this is already committed")` (line 171), whose message names only `this`. The message here names a target.
- The upstream comment's case (a typer state captured by a lazily forced `Message`): it is only tolerated when the target has errors or warnings, and the escape did not apply; no diagnostic was in play (the file is clean).
- `resume` committing the recorded state itself: `resume` never calls `commit`; only typer code does, into whatever `ctx.typerState` is.
- `completeSymbolsOf` or the Namer completers: a completer runs in its `creationContext` (`Namer.scala:940`), not in a `SkippedStat.ctx`; the stack would show `completeInCreationContext`. The request was a `resume`, not a completion.

### Reproduction (JUnit, `CompletionSessionSuite`)

The shape: a closure argument to a polymorphic method, whose body has a statement before the target that itself contains a polymorphic application (so the resume creates and commits a nested state with a new type variable). Request 1 targets the closure's last expression (skips the first statement under `tryEither`'s state, which is then committed). Request 2 targets inside the skipped statement.

```scala
  @Test def `a-resume-into-a-closure-body-does-not-commit-into-a-committed-state` =
    // I24. Request 1 types `run` along the path to `acc += x`: the closure
    // `xs.foreach { x => ... }` is typed by typedApply inside tryEither's
    // nested typer state, and the closure body's first statement is skipped
    // with that state recorded; the apply then succeeds and the state is
    // committed. Request 2 resumes into the skipped statement: `List(x, x)`
    // and `.foreach` create nested states under the committed one and commit
    // into it ("Attempt to commit TS[...] into already committed TS[...]").
    val code =
      """|object Com {
         |  def run(xs: List[Int]): Int = {
         |    var acc = 0
         |    xs.foreach { x =>
         |      if (x > 0) { List(x, x).foreach(y => acc += y); Option(x).map(_ + 1).foreach(acc += _) }
         |      acc += x
         |    }
         |    acc
         |  }
         |}
         |""".stripMargin
    val uri = URI.create("file:///Com.scala")
    val src = SourceFile.virtual(uri, code)
    val atLast = code.indexOf("acc += x") + 4
    val atInner = code.indexOf("List(x, x)") + 2
    val (sameRun, before, after, at) = withDriver { d =>
      d.runUpTo(uri, src, Span(atLast))
      val run0 = d.runIdOf(uri)
      val before = d.untypedSpans(uri).map(sp => code.substring(sp.start, math.min(sp.end, sp.start + 9)).trim)
      d.runUpTo(uri, src, Span(atInner)) // throws AssertionError before the fix
      val after = d.untypedSpans(uri).map(sp => code.substring(sp.start, math.min(sp.end, sp.start + 9)).trim)
      val unit = d.compilationUnits(uri)
      given Context = d.currentCtx.fresh.setCompilationUnit(unit)
      val path = Interactive.pathTo(unit.tpdTree, Span(atInner))
      (d.runIdOf(uri) == run0, before, after, path.headOption.map(_.tpe.widenTermRefExpr.show))
    }
    println(s"[a-resume-into-a-closure-body] same run: $sameRun; before: $before; after: $after; at List(x, x): $at")
    assert(sameRun, "the second request resumes the first request's run")
    assert(before.exists(_.startsWith("if (x > 0)")), s"the if is skipped by the first request: $before")
    assert(!after.exists(_.startsWith("if (x > 0)")), s"the if is typed by the second: $after")
    assert(at.exists(_.contains("List[Int]")), s"the resumed statement is typed with the right constraint: $at")
```

Two checks on the design before trusting a green run: (1) `before` must list the `if` (if `neededInBlock` or `nextAfterTarget` typed it in request 1, move the target or add an unrelated earlier statement); (2) if the assertion does not fire, confirm the skip happened under `tryEither` by logging `sk.ctx.typerState` (`isCommitted` is private; `toString`'s `X` after the resume is the tell) — if `foreach` resolved without `tryEither` on this build, replace `xs.foreach` by an overloaded method (`xs.map(...)`, or a user-defined `def each(f: Int => Unit)` plus `def each(f: (Int, Int) => Unit)`, which forces `typedArg` under an explore state and reproduces the sibling "not committable" assertion).

A second test for `completeSession`: the same file, request 1 as above, then `d.run(uri, src)` (the whole-file run that completes the session) and expect no exception.

### Candidate fix

Type the resumed statement under the nearest *live* ancestor of the recorded typer state, the idiom dotc itself uses when a prototype's creation state may have been committed since (`ProtoTypes.scala:501`: `inContext(protoCtx.withUncommittedTyperState)`, `Contexts.scala:528`, `TyperState.uncommittedAncestor` at `TyperState.scala:143-147`), extended to skip non-committable (explore) states too:

```scala
  // InteractiveDriver
  /** The recorded context of a skipped statement, with the nearest typer
   *  state that can still take constraints: a statement skipped inside an
   *  argument was recorded under tryEither's nested state, committed when
   *  the application succeeded (I24), or under an explore state.
   */
  private def liveContext(ctx0: Context): Option[Context] =
    def live(ts: TyperState): TyperState | Null =
      if ts.isCommittable && !ts.isCommitted then ts        // isCommitted needs a public accessor
      else ts.previous match { case null => null; case p => live(p) }
    live(ctx0.typerState) match
      case null => None
      case ts => Some(ctx0.withTyperState(ts))
```

`resume` and `completeSession` use `liveContext(sk.ctx)` in place of `sk.ctx`; `None` (no committable ancestor: a whole chain of explore states) falls back to a fresh run for that request (the pre-I20 rule for the statement), or in `completeSession` to leaving the statement skipped and poisoning the session. Diff summary: `TyperState` gains `def isCommitted: Boolean` (the field exists, private); `InteractiveDriver` gains `liveContext` and two call-site changes; `spliceAll`'s `using` context is unaffected (it does not type).

Why the live ancestor is the right state and not merely a tolerated one: at commit the nested state's constraint was merged into the ancestor and its type variables re-owned by it (`TyperState.commit`, lines 186-195), so the ancestor holds everything the closure's typing established plus what the enclosing application instantiated afterwards; the committed state holds a frozen prefix of that.

Residual, worth a sentence in the register: a statement skipped inside a `tryEither` branch that *failed* records a state that is neither committed nor dead by any flag (`isCommittable` stays true); the climb keeps it, and the resumed typing then runs in an abandoned branch whose constraints never propagate. Detecting that needs the typer to mark abandoned states (a `setCommittable(false)` on the fallback path of `tryEither` would do, and is cheap), or the resume to record the enclosing definition's context instead of the innermost one.

---

## I27: `assertion failed` in a whole-file run under Metals

### The new evidence: a second occurrence with a stack

`~/code/scratch/dotc-session-dotc/.metals/metals.log` line 2015 (build with the failed-request stack, 22:22:19), a whole-file `run` of `core/SymDenotations.scala` by `WithCompilationUnit` (document highlight at offset 1079), in a compiler instance whose previous requests were sessions on `Contexts.scala`, `Denotations.scala`, `DenotTransformers.scala` and targeted runs on `Main.scala`:

```
java.lang.AssertionError: assertion failed
    at dotty.tools.dotc.core.TypeOps$.dominators$1(TypeOps.scala:247)
    at dotty.tools.dotc.core.TypeOps$.approximateOr$1(TypeOps.scala:391)
    at dotty.tools.dotc.core.TypeOps$.orDominator(TypeOps.scala:409)
    at dotty.tools.dotc.core.Types$OrType.join(Types.scala:3626)
    at dotty.tools.dotc.core.Types$OrType.widenUnionWithoutNull(Types.scala:3642)
    at dotty.tools.dotc.core.Types$Type.widenUnion(Types.scala:1459)
    at dotty.tools.dotc.core.ConstraintHandling.widenInferred(ConstraintHandling.scala:702)
    at dotty.tools.dotc.typer.Namer.rhsType$1(Namer.scala:2320)
    at dotty.tools.dotc.typer.Namer.inferredResultType(Namer.scala:2339)
    at dotty.tools.dotc.typer.Namer.valOrDefDefSig(Namer.scala:1951)
    at dotty.tools.dotc.typer.Namer.defDefSig(Namer.scala:2087)
    at dotty.tools.dotc.typer.Namer$Completer.complete(Namer.scala:940)
    at dotty.tools.dotc.core.SymDenotations$SymDenotation.completeFrom(SymDenotations.scala:185)
    at dotty.tools.dotc.core.SymDenotations$SymDenotation.ensureCompleted(SymDenotations.scala:485)
    at dotty.tools.dotc.typer.Typer.retrieveSym(Typer.scala:3957)
    at dotty.tools.dotc.typer.Typer.typedNamed$1(Typer.scala:3982)
    ... typedBlockStats (Typer.scala:1624) ← typedDefDef (3248) ← typedClassDef (3590) ← typedClassDef (3590) ← typedPackageDef (3772) ×3
```

(The report `r_compiler-error_(dotc-session-dotc)_22-22-19-089.md` has the full stack at lines 3276-3355.) The assertion:

`core/TypeOps.scala:243-249`, inside `orDominator`:

```scala
    def dominators(cs: List[ClassSymbol], accu: List[ClassSymbol]): List[ClassSymbol] = (cs: @unchecked) match {
      case c :: rest =>
        ...
      case Nil => // this case can happen because after erasure we do not have a top class anymore
        assert(ctx.erasedTypes || ctx.reporter.errorsReported)
        defn.ObjectClass :: Nil
    }
```

A plain `assert(cond)` with no message, matching both reports. It fires when `commonBaseClasses = orBaseClasses(tp).filterConserve(isAccessible)` (line 389) is empty for an inferred union: `orBaseClasses` intersects the base classes of the alternatives (`TypeOps.scala:234-238`), and every class type has at least `Any` in its base classes, so an empty intersection means an alternative whose `baseClasses` is `Nil`: `Type.baseClasses` (`Types.scala:730`) gives `Nil` for anything that is neither a class type nor a type proxy, i.e. an `ErrorType` (`UnspecifiedErrorType` included), `WildcardType`, `NoType`, or a `TypeRef` whose denotation resolves to nothing (`info` = `NoType`). The invariant the assertion checks is "an error type exists only after an error was reported", and `errorsReported` is per reporter chain of the *current run* (`reporting/Reporter.scala:149`, `StoreReporter.scala:55`). So the failing run met an error-like type that no error of this run accompanies: a *silent* error type. The site is the completion of a local `def` without a result type (`retrieveSym` → `ensureCompleted` on a block statement of a method body) whose right-hand side is an `if`/`match` over such a type.

The 21:46:53 `Parsers.scala` failure is consistent with the same assertion: same bare message, same `WithCompilationUnit` whole-file path, 72.7 ms is enough for parse + index + the first members of `object Parsers` (the typer reaches a local `def` with an inferred result type early: `class ParserCommon`'s helpers), and in that instance `Contexts.scala` had been a targeted session (run 21, 143 skipped) left for `Synthesizer.scala` via `completeSymbolsOf`. The report keeps no stack, so this is inference; the second occurrence is the evidence.

### Why the retry "succeeded" (and what that says)

After each failure the log shows the next request at `run=3` (21:46: `Contexts.scala@8364 fresh run=3`; 22:22: the 651 ms whole-file run, then `SymDenotations.scala@1278 fresh run=3`). mtags' `CompilerAccess.withSharedCompiler` (`mtags-shared 1.6.9`, `scala/meta/internal/pc/CompilerAccess.scala:142-200`) calls `handleError` on any non-interrupt exception, which writes the `compiler-error` report and `shutdownCurrentCompiler()`; the next request loads a new `ScalaPresentationCompiler`, a fresh symbol table (the 651 ms, versus 56-300 ms for warm whole-file runs of similar files). So the retry says nothing about the file and everything about the instance: the state that made the union's alternative erroneous was accumulated across the previous runs of that instance and did not survive the restart. That rules the file's content out (it is the same snapshot that the x-ray typed four times over) and rules in the symbol table shared across runs.

### What persists across runs, and what the spike changed about it

Upstream's `InteractiveDriver` keeps the previous files' source-entered symbols in the package scopes across runs (a new run re-enters only the file it compiles; `ClassDenotation.enter` on a package scope unlinks the old entry). Two guards keep stale symbols from giving silent error types: `cleanup(tree, errorOutCompleters = true)` (`InteractiveDriver.scala:583-607`) sets `UnspecifiedErrorType` on every symbol in the typed tree still uncompleted at the end of a run, and `Namer.Completer.complete` (`typer/Namer.scala:934-938`) gives `UnspecifiedErrorType` to a completer run in a later run than its creation (asserting `Mode.Interactive`). Both are silent; upstream tolerates them because after a whole-file run nearly nothing is left uncompleted. (The working copy's `[I29-DBG]` print on the later-run branch is not in the committed patch, so whether the jar in the editor had it is unknown; no such line is in the Metals log either way, so the print cannot yet rule that branch in or out.) The spike adds, on top of the long-lived run of a session:

1. **Partial runs leave uncompleted symbols without erroring them out.** `run0` passes `errorOutCompleters = !partial` (`InteractiveDriver.scala:519-521`), and `completeSession` (`InteractiveDriver.scala:125-160`) never calls `cleanup`. `completeSymbolsOf` (`InteractiveDriver.scala:398-426`) walks the *skipped* statements when a file is left and completes their `DefTree`s. Its walk misses `untpd.ExtMethods` (`ast/untpd.scala:119`: `extends Tree`, not `DefTree`, so `case tree: untpd.DefTree if tree.hasAttachment(namer.ExpandedTree)` does not match and the methods under it are never completed; `Contexts.scala` has four `extension` blocks at lines 837-863 of the snapshot). A member left that way keeps a Namer completer of the left run; a later run touching it gets `UnspecifiedErrorType`, silently. This cannot be what happened in the 22:22 instance, though: every session there was completed by a whole-file run before its file was left (`skipped=0` on each `completes the session` line, lines 1947, 1999, 2011), so `completeSymbolsOf` had nothing to miss. It fits the 21:46 instance (`Contexts.scala` left with 143 skipped statements, four `extension` blocks among the file's members). A real hole either way, and the one a test can pin.
2. **A degraded info persists with its error reported in another run.** A symbol of a left file whose completion failed in run N (a prevented cycle caught by `Typer.typed`'s `handleTypeError`, `Typer.scala:4068-4081`, or "overloaded or recursive method needs result type") has an `ErrorType` info from then on (design doc §4 item 3: "the degraded value is cached as if it were right"). Run N reported the error; run N+k sees the type with `errorsReported` false. Upstream has the same exposure for files with real errors; the spike makes degraded infos more likely (targeted order, `completeSymbolsOf`'s completions with no body context, I17/I29's "not found" and `<error unspecified error>` answers were seen on these very files), and the session keeps the run alive longer.
3. **A completer re-run after a prevented cycle.** `unwindsInteractive` (`core/SymDenotations.scala:243-258`) clears `Touched` on a `CyclicReference` unwinding through an incomplete symbol, so the next touch runs its `Namer.Completer` again on an untyped right-hand side whose attachments the first attempt consumed (I8: `retrieveSym` removes `SymOfTree`, `typedAhead` caches `TypedAhead`). Upstream never re-runs a completer: `Touched` stays and every later touch throws again (and is reported). The re-run can yield `NoSymbol` owners, `UnAssignedTypeException` (the eleven 22:03 reports on `Contexts.scala` are that exception, from I28's stubbed inline body: a different cause, but the same family of "typed twice") or silent error types. Note `Contexts.scala:238` swallows a `CyclicReference` into `Nil` with no report, and `Types.scala:1326` into `safe_&`: a cycle prevented under either leaves no error behind.
4. **Classpath shadowing** (the question's candidate): the compiler jar and Bloop's output both hold `dotty.tools.dotc.parsing.Parsers`; the open file's source replaces the entry in the package scope (upstream mechanism), and the x-ray's test classpath differs only in which jar. I found no assertion in `SymbolLoaders`, `ClassfileParser` (`:766 assert(owner != null)` is for a missing outer, not a name clash), `Scopes.enter` (`:263 assert(e.tail != e)`, a structural check) or `Namer.enterSymbol`/`checkNoConflict` (reports an error, no assert) that a same-named source and classpath class could trip, and the x-ray typed the same file with the same shadowing. Not supported by the evidence, and the 22:22 stack is nowhere near loading.

Ranking: the assertion and its trigger (an alternative with `baseClasses == Nil` under an inferred union) are established; among the planters, 2 and 3 are the ones consistent with the 22:22 instance (no uncompleted leftovers, no later-run completer), 1 is consistent with the 21:46 instance (a session left with 143 skipped statements) and is the most testable; 4 is ruled out as far as reading goes. A definitive answer needs the symbol: a one-line probe before the assertion in `orDominator` that prints `tp` and the alternative whose base classes are empty (interactive mode only), which the x-ray's `hoverseq` over the same four files would then produce — but the x-ray already typed those four files without the failure, so the probe must run under Metals, where the instance accumulates many sessions first.

### Reproduction (JUnit, `CompletionSessionSuite`)

Two files in one driver, the first left after a targeted run with an `extension` block skipped (candidate 1), the second a whole-file run whose local `def` infers a union over the extension method's result. Without the fix, the extension method completes in the second run through the later-run branch to `UnspecifiedErrorType`, the union `Int | <error>` has no common base class, nothing was reported in that run, and `driver.run` throws the bare `AssertionError`.

```scala
  @Test def `leaving-a-file-completes-its-extension-methods` =
    // I27 candidate: completeSymbolsOf walks DefTrees, and an `extension`
    // block is an ExtMethods, not a DefTree, so its methods keep the left
    // run's Namer completers; the next run gives them UnspecifiedErrorType
    // silently, and an inferred union over such a type trips
    // TypeOps.orDominator's `assert(ctx.erasedTypes || ctx.reporter.errorsReported)`.
    val uriA = URI.create("file:///ExtA.scala")
    val uriB = URI.create("file:///ExtB.scala")
    val codeA =
      """|object ExtA {
         |  extension (s: String) def twice = s.length * 2
         |  def n = 1
         |}
         |""".stripMargin
    val codeB =
      """|object ExtB {
         |  import ExtA.*
         |  def run(b: Boolean): Int = {
         |    def pick = if b then "x".twice else 0
         |    pick
         |  }
         |}
         |""".stripMargin
    val (diags, tpe) = withDriver { d =>
      d.runUpTo(uriA, SourceFile.virtual(uriA, codeA), Span(codeA.indexOf("def n") + 5))
      val diags = d.run(uriB, SourceFile.virtual(uriB, codeB)) // AssertionError before the fix
      val unit = d.compilationUnits(uriB)
      given Context = d.currentCtx.fresh.setCompilationUnit(unit)
      val path = Interactive.pathTo(unit.tpdTree, Span(codeB.indexOf("\"x\".twice") + 5))
      (diags.map(_.msg.message), path.headOption.map(_.tpe.widenTermRefExpr.show))
    }
    println(s"[leaving-a-file-completes-its-extension-methods] diagnostics: $diags; twice: $tpe")
    org.junit.Assert.assertEquals(Nil, diags)
    org.junit.Assert.assertEquals(Some("Int"), tpe)
```

If `twice` is typed `Int` even before the fix, the extension method was reached some other way (check `completeSymbolsOf`'s walk with a print of what it completes); then move to candidate 2 with a stronger test: make `ExtA` degrade on purpose (a real cycle, `def a = b; def b = a` without result types, both skipped in the targeted run), leave the file, and in `ExtB` infer `def pick = if b then ExtA.a else 0`: the second run sees `a`'s `ErrorType` from the first run's reported cycle, and the same assertion fires. That second test documents upstream's exposure made common by the session; the first documents the spike's own hole.

For Metals itself: the deterministic replay is the 22:22 sequence on a fresh PC (`Contexts.scala` session → `Denotations.scala` sessions → `DenotTransformers.scala` sessions → `Main.scala` hover → document highlight on `SymDenotations.scala`), which the x-ray's `hoverseq` could script, with the `orDominator` probe above in the jar.

### Candidate fix

Three layers, cheapest first:

1. **`completeSymbolsOf` walks `ExtMethods` and other non-`DefTree` carriers of definitions.** In `walk`, add `case tree: untpd.ExtMethods => tree.getAttachment(namer.ExpandedTree).foreach(walk)` (its expansion is a `Thicket` of `DefDef`s with `SymOfTree`), and treat `untpd.Thicket` and `untpd.PatDef`'s expansion the same way (PatDef is a DefTree; its expansion is handled; ExtMethods is not). Same change in `completeClassesOfUnit` (`SymDenotations.scala:1932-1960`), which has the same `walk`. One-line diff each.
2. **Restore the invariant where the spike breaks it.** In `Namer.Completer.complete`'s later-run branch (`Namer.scala:934-938`), report an error on the symbol's position ("`$denot` of `${file}` was left incomplete by an earlier request") before giving `UnspecifiedErrorType`; the diagnostic goes to the current run's reporter (`errorsReported` becomes true), is removed with the run's buffered messages, and makes the I7/I17/I29 family visible instead of silent. Likewise `cleanup`'s `errorOutCompleters` could report under `Mode.Interactive`. This does not cover candidate 2 (an `ErrorType` whose error was reported in an earlier run); for that, the honest rule is the design doc's: a degraded info must not outlive the run that produced it. The cheapest form: when a file is left, **unlink its top-level symbols from their package scopes** (`pkg.unforcedDecls.unlink(sym)` for each `SymOfTree` of the unit's top-level statements, after `completeSymbolsOf`) so that other files resolve the names to the classpath entries again (the Bloop output / jar hold the same classes, which is Metals' normal situation for closed files); the next request on the file re-enters them. That is a behaviour change from upstream (other open files currently see the left file's *source* symbols, with their completed infos), to be measured: Metals' PC compiles one file at a time and reads the rest from the classpath anyway.
3. **Tolerate in interactive mode, as upstream does elsewhere.** `assert(ctx.erasedTypes || ctx.reporter.errorsReported || ctx.mode.is(Mode.Interactive))` at `TypeOps.scala:247`, falling to `defn.ObjectClass :: Nil` (the inferred type degrades to `Object`/`AnyRef`). `Typer.scala:2506, 3072, 3807` and `Types.scala:3231` are the same shape and would need the same guard to be consistent. Worth doing regardless (a PC must not die on a degraded symbol), but it hides the planter, so it belongs after 1 and 2 and together with the `orDominator` probe that prints the offending alternative under `-Ddotty.interactive.cycleStats=true`.

### Confidence

- That the bare assertion in both Metals failures is `TypeOps.scala:247`: high for 22:22 (the stack), moderate for 21:46 (same message, path and timing; no stack).
- That the planter is accumulated instance state rather than the file: high (the restart-on-error policy, the run-id reset, the x-ray typing the same files).
- Which spike change plants the silent error type: candidate 1 for the 21:46 instance and 2/3 for the 22:22 instance are plausible, none demonstrated. The test above decides candidate 1 in one run; a probe under Metals decides the rest.
