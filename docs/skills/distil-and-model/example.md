# A complete climb: a presentation compiler interrupted mid-check

One mechanism taken from a real bug through a toy, a model and back, as the shape to imitate. Each section is a rung of the skill; the code is condensed from the real artefacts but every shape is real.

## 1. The real system and the bug

scalac's interactive compiler (the one behind IDE completions) types the loaded files on one thread. After every tree it types, the typer calls `signalDone`, and there, if no completer is in progress (`lockedCount == 0`) and no region has asked to be left alone (`interruptsEnabled`), it services the requests that have arrived, *inside* the type check in progress, on the same thread, against the same symbol table. A completion request types the file up to the tree at the cursor and unwinds; a reload starts a new run and unwinds the background check.

A PR fixing a family of flaky presentation-compiler tests made five changes. Read for the kind of state each one repairs:

| change | the state, which is not a cached fact | the invariant broken at a safepoint |
|---|---|---|
| make `addSyntheticMethods` uninterruptible | a case class's member set, grown in a burst of four with a safepoint after each | the burst is all-or-nothing ("already has … not adding"): a nested request saw part of it and skipped the rest |
| make `addSynthetics` uninterruptible, keep consumed trees | a per-run map of synthetic trees, **consumed** when a tree is added to a body | a nested full check took the remaining trees; a targeted check consumed them and was abandoned |
| keep the implicit factory symbol | a symbol's **identity**, replaced each time its template was typed | the run's implicit cache held the old symbol, now reported as shadowed |
| suspend a targeted check's warnings | a flag claiming every `@nowarn` in the file is known | a targeted check that stopped early made the claim |

The reviewer's question was whether a soak test with random interleavings would pass. That question is the rest of the climb. The mechanism's state is small (a burst, a consumed map, an identity cache, a completeness flag) and its order is "which safepoint the request lands at"; the invariant is that the answer does not depend on it.

## 2. The survey

Two other systems service requests mid-check and take different positions:

| | scalac | dotc under Metals | IntelliJ PSI |
|---|---|---|---|
| where a request runs | nested, at `signalDone` | a fresh run of the file per request; requests queue, nothing is interrupted | its own thread, as a read action |
| black hole on re-entry | a `LOCKED` flag reset in a `finally`, so an abort leaves the symbol forceable | a `Touched` flag, not reset on unwind: an aborted symbol is a cyclic reference for the rest of the run | a recursion guard that answers `null` and forbids caching above the re-entered frame |
| cancellation | `CancelException` unwinds to the run loop | the interrupt bit is read at unit boundaries only, and the IDE never sends one | a pending write cancels every read at its next checkpoint; the read restarts |
| what it pays | a safepoint invariant over all mutable state | whole-file retyping per request | read actions may write nothing but pure caches |

Two findings came from reading alone and needed no toy: dotc's cancellation callback can never fire (its checkpoint consumes the interrupt bit before asking the callback), and IntelliJ's guard caches the re-entered frame itself, so for two values that each read the other the cached one depends on which was asked first.

## 3. The toy

The language has classes, objects and traits with members, and no expressions. A member's type is declared or inferred from a path, and inference is what forces other facts, which is what a request lands inside. Case classes get synthetics in a burst and through a consumed map, implicit classes get a factory, members can be deprecated, objects can be `@nowarn`: exactly the state in the PR's table, nothing else.

```
// scenario case-class-completion.toy
// event: completion A Use.f
// file: A
class Int {}
case class L(a: Int) { def self: L }
object Use {
  def l: L
  def f = l.self
}
```

The shared state is one class, about 500 lines of plain Java: symbols with completers, `force` with the black hole, a namer per run, a typer that calls `signalDone` after each member, each synthetic and each class, and a `Policy` of six booleans (the four the PR changed, plus "reset the black hole on unwind" and "reuse symbols across runs", where scalac and dotc differ).

```java
protected void signalDone(Unit unit, String where, Target reached) {
  Event ev = scheduler.at(where);                    // the harness injects here
  if (ev != null) onEvent(ev);
  if (!interruptsEnabled || lockedCount > 0) return;  // scalac's two guards
  if (reached != null && reached.equals(unit.target))
    throw new TyperResult(completionAnswer(unit, reached));
  checkForMoreWork(where);                            // service the queue, nested
}
```

Every line of that is a claim about scalac, written down beside the file: "the burst is `copy`, `equals`, `hashCode`, `toString`"; "the implicit factory is entered by the typer". Two of those claims were wrong, and §7 says how that was found.

## 4. Kernels and the harness

Each surveyed design is a `Kernel` over the same `Global` with `reload`, `send(event)` and `drain()`:

| kernel | where a request runs | models |
|---|---|---|
| `scalac-before`, `scalac-after` | nested at `signalDone`; a targeted check unwinds with `TyperResult` | scalac before and after the PR's four policy bits |
| `dotc-metals` | a fresh run per request, never interrupted, a cache keyed on the last file | dotc under Metals |
| `dotc-interrupted` | as above, but an interrupt lands at the next checkpoint and the driver is kept | a hypothetical: what if the IDE did interrupt |
| `psi` | stubs by name; cached values under a modification count with the recursion guard; an edit cancels the reader | IntelliJ |

The harness is the soak test the reviewer asked for, exhaustive rather than random. Count the background's safepoints on a fresh kernel; take the reference answers from a fresh kernel with the event sent *after* the background; then for each safepoint `k`, a fresh kernel with the event injected at `k`, and compare.

```java
int K = countSafepoints(scenario);                   // fresh kernel, no event
List<String> reference = answersAfterBackground(scenario);
for (int k = 0; k < K; k++) {
  Kernel kern = fresh(scenario, fireAt = k);
  List<String> got = kern.drain();                    // the event lands at safepoint k
  got.addAll(loadedTypedOfEveryFile(kern));           // what later requests will see
  if (!got.equals(reference)) divergent.put(k, got);
}
```

The oracle is metamorphic: the answer must not change when the request moves. The committed results file, regenerated by the run script, is a table of divergent safepoints per scenario per kernel:

| scenario (the PR test it mirrors) | scalac-before | scalac-after | dotc-metals | dotc-interrupted | psi |
|---|---|---|---|---|---|
| case-class-completion | 7/16 | 0/16 | 0/16 | 0/16 | 0/19 |
| case-class-loaded (a whole-file request, nested) | 16/16 | **16/16** | 0/16 | 0/16 | 0/19 |
| targeted-consumes-synthetics | 8/18 | 0/18 | 0/18 | 0/18 | 0/20 |
| implicit-class | 10/17 | 0/17 | 0/17 | 0/17 | 0/16 |
| nowarn | 13/14 | 0/14 | 0/14 | 0/14 | 0/14 |
| edit-cross-file | 0/11 | 0/11 | 0/11 | **5/11** | 0/11 |

The PR's four fixes close the four shapes they target, by the mechanism the commit messages describe. Two things the PR did not cover appear: a whole-file request served nested still diverges at every safepoint (a prediction, later confirmed on scalac with a test in the PR's own shape), and the hypothetical interrupted dotc goes wrong only through its last-file cache. This is already more than the PR's tests knew. It is still seven hand-written scenarios.

## 5. The model

The toy's facts sit on a small theory: a fact has a rule that asks other facts, forcing runs the rule once and stores the result, and forcing a fact that is on the stack is a black hole.

```lean
def force (R : Rules Q V) : Nat → List Q → Store Q V → Q → Out Q V × Store Q V
  | 0, _, s, _ => (.fuel, s)
  | n + 1, stk, s, q =>
    match s q with
    | some v => (.ok v, s)
    | none =>
      if q ∈ stk then (.cyc q, s)
      else match runWith (fun s' q' => force R n (q :: stk) s' q') (R q) s with
        | (.ok v, s') => (.ok v, upd s' q v)
        | (e, s') => (e, s')
```

Over that theory, interruptibility is free: every intermediate store of a forcing cut at any point agrees with the semantics, so abort and restart is sound, and a request serviced with an empty stack is a reordering of demands with the same answers. That theorem says the bugs are all outside the facts, which the PR's table had already said in other words. The model earns its keep on the next two layers.

**The namer as rules.** A function from any program of the toy language to the rules of its facts: a class's member names, its parent, each member's type. A `Cut` says how a compiler bundles them (scalac looks a member up without its info; dotc forces it, and reads a member set in progress as the names indexed so far). This is where the theorems start quantifying over programs rather than over hand-written rule sets.

**The kernel as a state machine.** The Java kernel ported line for line where it matters, with every force of a member's type taken from the namer's rules, and everything else as state: the burst, the consumed map, the implicit factories' generations, the suspended warnings, the targeted check, and the scheduler. Exceptions run over the state, so an abandoned check keeps what it did, which is the whole point.

```lean
structure Policy where
  uninterruptibleSynthesis : Bool
  keepSyntheticsForTargeted : Bool
  keepFactory : Bool
  suspendTargetedWarnings : Bool
  idempotentSynthetics : Bool      -- the proposal: regenerate what a tree lacks

def signalDone ... : K Unit := do
  let k := (← get).count
  modify fun st => { st with count := k + 1, trace := st.trace ++ [where_] }
  if st.fireAt == some k then enqueue st.event           -- the harness
  if !serviceable || !st.interruptsEnabled then return
  if reached == st.target then throw (.typerResult (← completion f t))
  poll nested

def divergent (policy : Policy) (sc : Scenario) : List Nat :=
  let ref := reference policy sc
  (List.range (safepoints policy sc)).filter fun k => atSafepoint policy sc k != ref
```

## 6. Conformance: the results file is a theorem

```lean
theorem results_before_after_proposed :
    scenarios.map (fun sc => (sc.name, safepoints .before sc,
                              divergent .before sc, divergent .after sc, divergent .proposed sc)) =
      [("case-class-completion", 16, List.range 7, [], []),
       ("case-class-loaded",     16, List.range 16, List.range 16, []),
       ("cycle",                 12, [], [], []),
       ("edit-cross-file",       11, [], [], []),
       ("implicit-class",        17, [0, 1, 2, 3, 4, 5, 6, 14, 15, 16], [], []),
       ("nowarn",                14, List.range 13, [], []),
       ("targeted-consumes-synthetics", 18, List.range 8, [], [])] := by
  decide +kernel      -- about 25 s

theorem caseClassCompletion_trace :
    backgroundTrace .before caseClassCompletion =
      ["class Int", "rhs L.self", "member L.self", "synth L.equals", "synth L.hashCode",
       "synth L.toString", "class L", "synthetic <toplevel>.L", "synthetic object L.apply",
       "synthetic object L.unapply", "synthetic class L.copy", "rhs Use.l", "member Use.l",
       "rhs Use.f", "member Use.f", "class Use"] := by
  decide +kernel
```

The first says the numbers agree; the second says the safepoints are the same ones, by name and in order, which is what makes the numbers comparable. The first port disagreed with the Java toy on one count: 11 safepoints for the cycle scenario against 12. Neither side was edited to match. scalac was read: on a cyclic reference every completer on the stack is given an error type as the error propagates up, and each ends with its own `signalDone`; 12 was right, and the port's forcing now returns the stack at the cycle.

## 7. The space: where the model pays

The Lean kernel runs a scenario in milliseconds, so the harness runs over every program assembled from a menu, in every order, with every request:

```lean
def menu : List Decl := [
  caseClass "L" [param "a" "Int"] [m "self" "L"],
  object "L" [m "mk" "L"],                         -- a companion of its own
  implicitClass "RichInt" [param "i" "Int"] [m "twice" "Int"],
  object "Use" [m "l" "L", inf "f" ["l", "self"], m "three" "Int", inf "g" ["three", "twice"]],
  caseClass "M" [param "b" "Int"] [m "l" "L", inf "h" ["l", "self"], inf "k" ["l", "a"]],
  class_ "Old" [deprecated (m "m" "Int")],
  nowarnObject "Later" [m "o" "Old", inf "bar" ["o", "m"]],
  object "Use2" [m "o" "Old", inf "foo" ["o", "m"], m "l" "L", inf "f2" ["l", "self"]]]

def programs := (selections 2 menu ++ selections 3 menu).map (intD :: ·)   -- every order
def space := programs.flatMap fun p => (requests p).map (scenario p)         -- 1,372
```

**It debugged the toy first.** The first run reported divergences under the proposed policy for programs with the implicit class or the case class declared *after* its consumer, which the proposal was meant to close. Reading scalac for those programs: the implicit factory is entered by the namer, not the typer; `copy` is the namer's synthetic too, through the consumed map like `apply` and `unapply`; and a replaced factory's tree is never found by the method that walks the scope. The Java toy had all three wrong, and the port had copied it faithfully, which is why conformance had not caught it. Both were fixed, the results file regenerated, the theorem restated; two numbers in the seven-scenario table moved by one.

**Then it found the shape no policy closes.** Before the PR 755 scenarios diverge; after it 369, of which 312 are the whole-file family and 57 are completions; under the proposal the same 57. Every one of the 57 has the case class declared after the member whose completion is asked, and diverges at exactly the safepoints before the class's burst: a targeted check types the file up to its target and never reaches the class, so the completion lists it as the namer left it, without the typer's overrides. That is a *targeting* gap, not a synthetics policy, and it is the finding the seven hand-written scenarios could not have made, because each of them was written with the case class first.

**And it stated the obligations of a design nobody had built.** A second way to serve a request on the same kernel, abort the background and restart it, with cleanup bits as the design's obligations, each a theorem over all seven scenarios at every safepoint:

| mode | what diverges | the obligation it names |
|---|---|---|
| abort, no cleanup, PR's policy | the burst once begun, the consumed trees | the frames that are not resumable: where the `finally`s go |
| abort, no cleanup, idempotent synthetics | nothing | a check that regenerates what its tree lacks has nothing to restore |
| abort + restore the unit's state | the warnings and the cyclic-reference errors | diagnostics are a consumed side effect of fact completion: a restart that keeps the facts must keep what they reported |
| abort + restore, diagnostics kept with the facts | nothing | the design, complete |

The third row was not foreseen. It became the first item in the design note for the real system.

## 8. Projection back

* The whole-file prediction, confirmed on the PR's head with a test in the shape of the PR's own: a `signalDone` hook that serves the request at a chosen safepoint, then a comparison of the tree. Two runs, failing on the clean head, passing with the patch the model's obligations named (per-check state for the consumed maps). A first "confirmation" from a tree that still had the patch applied was discarded; the rule that a confirmation is two runs on a named commit comes from that.
* For dotc, the abort-and-restart design as a patch: a sticky cancellation flag polled inside the typer, an exception that unwinds, and four `finally`s, the one for `Touched` being the theorem about the black hole discipline made concrete. Three new tests and the existing suites pass. The control run with that `finally` disabled reproduces the model's prediction on the real compiler: the next completion on the file is empty.
* The spikes found three things the toy could not: a completer refuses to run in a later run than its own, typing an untyped tree consumes attachments so it is not idempotent, and a completion's cost on a wide file is the import search, not typing. Each is in something the toy left out (run identity, attachments, the search after the mechanism), which is what §"What it cannot do" of the skill means.

## 9. The register

Nine rows, each with the system, the evidence (a scenario, a theorem, a test), a status (triage, draft, filed, no action) and a next step. Two are confirmed on scalac with tests; two are patches on dotc passing its suites; one is confirmed by reading platform source; four are in triage with the test that would settle each named.

## 10. The next rung, on this floor

This climb was itself the second: the theory of lazy facts with a black hole came from the previous question (why a well-founded program gets a cyclic-reference error in one compiler and not another, and why a wildcard export silently drops a member by file order), whose theorems quantified over rule sets written by hand. The interruption question added a layer beneath the kernel (abort budgets, a touched set in place of the stack, taint on peeked answers) and proved it for every rule set; then the namer as rules over programs let the previous climb's two hand-written findings be restated as theorems over the programs that showed them.

The questions after this one, each answered on the same floor until it gave way:

| question | where it went | what it needed |
|---|---|---|
| abort and restart instead of nested servicing | one `Mode` on the same kernel; four theorems over the same seven scenarios | nothing new in the language |
| a targeted, resumable session for the never-interrupting design | one more kernel in the Java toy with a `runUpTo`, and a replay harness over an editing session | an edit event that appends to a file |
| facts that outlive a run, re-validated by the trace they recorded | a new layer between the theory and the kernel: facts keyed by revision | the theory's existing trace theorem, applied to the namer's rules |
| which subtrees a request may leave untyped, and what an edit inside a body invalidates | a new toy | trees with positions, an edit as a tree replacement, a dependency from facts to subtrees: the first three items of this toy's "cannot do" list |

The rule the sequence shows: stay on the floor while the existing language forces the new state, add a layer when the question is about what facts are keyed by, and start a new toy when the question is about what the old one abstracted away.

## Why the model step was worth it, in one paragraph

The toy alone reproduced the PR's bugs and predicted one more. The model ran a space the toy could not have run in reasonable time, and the space did three things the toy could not: it found the toy's own fidelity errors, by producing programs the toy's author had not thought to write; it isolated the one shape that survives every policy, which is a statement about the mechanism and not about a fix; and it stated the obligations of a design that did not exist yet as theorems, one of which nobody had anticipated. The conformance theorem is what makes those results about the toy, and the real system's tests are what make them about scalac.
