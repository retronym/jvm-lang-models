# The theorems

The canonical statement of the obligations and T1–T5; other documents point here.

**The obligations.** A compiler is a per-unit task that queries an oracle, plus a bridge: `keys` (what it records), `π` (a hash per key) and `covers` (which queries a key vouches for). On [`XCompiler`](../packages/inc-comp/IncComp/General.lean#L22) ([`XCompiler.Obligations`](../packages/inc-comp/IncComp/General.lean#L46)):

- **comp** (compositionality): joint compilation of a group is a fixed point of the per-unit tasks, with group-mates answered from their fresh interfaces;
- **coverage**: every traced query, misses included, is covered by a recorded key;
- **abstraction**: equal hashes on a key give equal answers to every query it covers;
- **locality**: a key's hash reads only the interfaces in its declared `hashDeps`.

The local [`IncComp.Compiler`](../packages/inc-comp/IncComp/Model.lean#L28) has the first three. The policy's one obligation is [`Policy.Sound`](../packages/inc-comp/IncComp/Model.lean#L119): never drop an invalidated unit outside the round just compiled.

| | Name | Statement | Hypotheses |
|---|---|---|---|
| T1 | [`Task.run_eq_of_trace`](../packages/query/Query/Task.lean#L40) | Oracles that agree on a run's trace give the same output and trace | none |
| T2 | [`XCompiler.round_preserves`](../packages/inc-comp/IncComp/General.lean#L109) | One round, with `Δ` over the affected units, preserves the invariant | the obligations; dirty set `D ⊆ R` |
| T3a | [`XCompiler.zinc_sound`](../packages/inc-comp/IncComp/General.lean#L242) | If the loop returns, every unit is up to date: a per-unit fixed point | plus [`Policy.Sound`](../packages/inc-comp/IncComp/Model.lean#L119) |
| T3b | [`Compiler.fixpoint_unique_of_wf`](../packages/inc-comp/IncComp/Uniqueness.lean#L66), `_of_explicit` | Per-unit fixed points are unique | traced dependencies well-founded under every oracle, or every interface a function of the source alone |
| T3 | [`Compiler.zinc_eq_clean_of_wf`](../packages/inc-comp/IncComp/Uniqueness.lean#L122), `_of_explicit` | Incremental = clean | T3a's and T3b's; on `Compiler`, and on [`TCompiler`](../packages/inc-comp/IncComp/Tree.lean#L26) through `toCompiler` (`:189`, `:204`) |
| T4 | [`XCompiler.zinc_some_of_monotoneFrom`](../packages/inc-comp/IncComp/General.lean#L291); [`Compiler.zinc_some_of_explicit`](../packages/inc-comp/IncComp/Termination.lean#L99), `_of_wf` | The loop returns within a bound: `k + \|S\| + 1` rounds; 2; height + 2 | a policy monotone from round `k` (`transitiveStep`); or T3b's hypotheses, `Compiler` only |
| | [`PingPong.zinc_diverges`](../packages/zinc/Zinc/Loop/PingPong.lean#L219) | Without `transitiveStep`, Zinc's loop diverges for every fuel on three mutually inferred classes | kernel `decide` |
| T5 | [`XCompiler.downstream_sound`](../packages/inc-comp/IncComp/General.lean#L389) | A downstream subproject's loop, seeded from changed sources and external invalidations, ends sound against the new classpath | fresh snapshots; T5a `inv_external` (`:281`) needs only abstraction |
| | [`Stale.stale_unsound`](../packages/inc-comp/IncComp/Stale.lean#L132), [`stale_affected`](../packages/inc-comp/IncComp/Stale.lean#L137) | T2-stale: a non-local hash diffed over the recompiled set alone undercompiles; over `affected` it does not | kernel `decide` |
| | [`Cycles.zinc_ne_clean`](../packages/zinc/Zinc/Loop/Cycles.lean#L191), [`annotated_eq_clean`](../packages/zinc/Zinc/Loop/Cycles.lean#L220) | T3a without T3 for inferred types in a cycle; T3 when every member is annotated | |
| B4 | [`XCompiler.untouched_eq_clean`](../packages/inc-comp/IncComp/General.lean#L578) | A unit Zinc never recompiles equals the clean build's, so it links as a fresh build does | explicit interfaces, through [`XCompiler.fixpoint_unique_of_explicit`](../packages/inc-comp/IncComp/General.lean#L547) (`:100`) |
| | [`zinc_sound_charged`](../packages/zinc/Zinc/Loop/Files.lean#L176) | T3a with file-closed rounds and imports charged to one class of the file | charged obligations; file-closed policy |

**Laziness (Track L).** A compiler's symbol table as a lazy evaluator ([`Query.Lazy`](../packages/query/Query/Lazy.lean), [`Query.Freeze`](../packages/query/Query/Freeze.lean); [`track-l.md`](../packages/scala/docs/track-l.md)):

| Name | Statement | Hypotheses |
|---|---|---|
| [`Lazy.force_ok`](../packages/query/Query/Lazy.lean#L111) | Forcing any fact from any consistent store returns its value and never black-holes | a ranked fixed point of the rules (well-founded definitions) |
| [`Lazy.forceAll_ok`](../packages/query/Query/Lazy.lean#L160) | Every order of demands gives the same answers | the same |
| [`Lazy.cycle_unranked`](../packages/query/Query/Lazy.lean#L176) | A black hole means no ranking puts the fact below the fuel | none |
| [`Lazy.phase_ranked`](../packages/query/Query/Lazy.lean#L199) | Facts indexed by phase rank lexicographically | no fact reads a later phase; reads within a phase ranked |
| [`Freeze.guarded_quasi_det`](../packages/query/Query/Freeze.lean#L67) | A pushed fact whose reads freeze it gives every read the whole fact, whatever the order, or the run fails | none |

**Interruptibility (Track I).** A presentation compiler over those facts ([`Query.Interrupt`](../packages/query/Query/Interrupt.lean); [`track-i.md`](../packages/scala/docs/track-i.md) §7):

| Name | Statement | Hypotheses |
|---|---|---|
| [`Interrupt.forceA_agree`](../packages/query/Query/Interrupt.lean#L158) | Every intermediate store of a forcing cut at any safepoint agrees with the semantics and keeps every finished fact, under either black-hole discipline | a fixed point of the rules (no ranking) |
| [`Interrupt.abort_restart_ok`](../packages/query/Query/Interrupt.lean#L208) | Restarting from an aborted store gives the same answers | a ranked fixed point |
| [`Interrupt.forceA_unlock_touched`](../packages/query/Query/Interrupt.lean#L315), [`abort_touched`](../packages/query/Query/Interrupt.lean#L269), [`touched_stays_cyclic`](../packages/query/Query/Interrupt.lean#L287) | scalac's `finally unlock()` leaves the black holes as found; dotc's `Touched` makes an aborted fact a cyclic reference for the rest of the run | none |
| [`Interrupt.nested_empty_stack_reorders`](../packages/query/Query/Interrupt.lean#L378) | A request serviced with nothing in progress is a reordering of demands, with the same answers | a ranked fixed point |
| [`Interrupt.nested_inside_frame_cycles`](../packages/query/Query/Interrupt.lean#L415) | Serviced inside a frame, it can black-hole on a fact the rules rank | kernel `decide` |
| [`Interrupt.forcePeek_ok`](../packages/query/Query/Interrupt.lean#L467) | Under ranked rules no peek ever finds its fact in progress; the store agrees | a ranked fixed point, peeks read as forces |
| [`Interrupt.forceT_agree`](../packages/query/Query/Interrupt.lean#L668) | With full taint (nothing computed from an `absent` is memoized) every stored value is the fixed point's, cyclic programs included | a fixed point, peeks read as forces |
| [`Interrupt.forcePeek_memoizes_order`](../packages/query/Query/Interrupt.lean#L739), [`psi_root_order_dependent`](../packages/query/Query/Interrupt.lean#L748), [`fullTaint_stores_nothing`](../packages/query/Query/Interrupt.lean#L755) | `forcePeek` memoizes an order-dependent answer; IntelliJ's rule memoizes the re-entered frame's; full taint memoizes nothing on the cycle | kernel `decide` |
| [`Interrupt.burst_allOrNothing_whole_iff`](../packages/query/Query/Interrupt.lean#L797), [`consuming_add_one_owner`](../packages/query/Query/Interrupt.lean#L848), [`keep_cache_sound`](../packages/query/Query/Interrupt.lean#L884) | The three non-fact shapes of [scala/scala#11328](https://github.com/scala/scala/pull/11328): a burst read at a safepoint inside it, a consumed map over all interleavings of two checks, an identity cache under every schedule | kernel `decide`; [`keep_cache_sound`](../packages/query/Query/Interrupt.lean#L884) for every schedule |

**The toy language's namer (Track I meets Track L).** The lazy facts of any program of the Java toy's language, as a function of the program and of how a compiler bundles them ([`ScalaTypes.ToyNamer`](../packages/scala-types/ScalaTypes/ToyNamer.lean); [`track-i.md`](../packages/scala/docs/track-i.md) §8):

| Name | Statement | Hypotheses |
|---|---|---|
| [`ToyNamer.rulesOf`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L274) | The namer: the rule of every fact (member names, parent, each member's type) of a program, under the `fine`, `scalac` or `dotc` cut | a definition |
| [`ToyNamer.l9_dotc_order_dependent`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L338), [`l9_fine_order_free`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L344) | L9: under dotc's cut `A`'s member set has the forwarder `b` with `A.scala` typed first and not with `B.scala` first; under the fine cut both orders agree | kernel `decide` |
| [`ToyNamer.l9_taint_order_free`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L354) | Under full taint the answer is the same in both orders, and nothing on the cycle is stored | kernel `decide` |
| [`ToyNamer.l2_dotc_order_dependent`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L377), [`l2_fine_cycle`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L386) | L2: mutual exports conflict with `A.scala` first and compile with `B.scala` first under dotc's cut; under the fine cut the member sets are a true cycle in both orders | kernel `decide` |
| [`ToyNamer.cycleToy_all_cuts`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L401), [`implicitToy_order_free`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L416), [`caseToy_names`](../packages/scala-types/ScalaTypes/ToyNamer.lean#L428) | The Java toy's `cycle`, `implicit-class` and `case-class` scenarios: a true cycle under every cut, the implicit view order-free under every cut, the synthetics names the namer has | kernel `decide` |

**The scalac kernel over the namer (Track I).** `Scala2Kernel.java` as a state machine over the namer's facts, with the Java harness ([`ScalaTypes.ToyKernel`](../packages/scala-types/ScalaTypes/ToyKernel.lean); [`track-i.md`](../packages/scala/docs/track-i.md) §9):

| Name | Statement | Hypotheses |
|---|---|---|
| [`ToyKernel.caseClassCompletion_trace`](../packages/scala-types/ScalaTypes/ToyKernel.lean#L765) | The kernel's safepoints for `case-class-completion` are the Java kernel's, by name and in order | kernel `decide` |
| [`ToyKernel.results_before_after_proposed`](../packages/scala-types/ScalaTypes/ToyKernel.lean#L774) | For the seven scenarios of `results.txt`, the background's safepoint counts and the divergent safepoints under the policies before [scala/scala#11328](https://github.com/scala/scala/issues/11328), after it and the proposal are exactly the Java harness's | kernel `decide` |
| [`ToyKernel.abort_proposed_safe`](../packages/scala-types/ScalaTypes/ToyKernel.lean#L737) | With abort-and-restart and idempotent synthetics, no scenario diverges at any safepoint, with no cleanup | kernel `decide` |
| [`ToyKernel.abort_after_not_resumable`](../packages/scala-types/ScalaTypes/ToyKernel.lean#L743) | Under the PR's policy an abort after the burst began or after synthetic trees were consumed leaves the restart short | kernel `decide` |
| [`ToyKernel.abort_restore_loses_diagnostics`](../packages/scala-types/ScalaTypes/ToyKernel.lean#L751) | A top-level restore repairs the consumed maps and loses the diagnostics completers emitted, since the memoized facts never re-emit them | kernel `decide` |
| [`ToyKernel.abort_restore_keep_safe`](../packages/scala-types/ScalaTypes/ToyKernel.lean#L759) | Restore everything but what the completers reported, and nothing diverges under the PR's policy or the proposal | kernel `decide` |
| [`ToySpace.consumerFirst_safepoints`](../packages/scala-types/ScalaTypes/ToySpace.lean) | The consumer-first scenario has twenty safepoints; its twelve divergent ones under the proposal are observed by `#eval` (`decide +kernel` is stuck on it: open) | kernel `decide` |

## Where the hypotheses bite

- Abstraction is perfect hashing: collisions of Zinc's 32-bit name hashes are excluded by fiat.
- T3's well-founded case covers every traced query under every oracle, which rules out self-queries and body-level cycles; uniqueness should need only that the dependencies affecting interfaces are well-founded ([sbt/zinc#1284](https://github.com/sbt/zinc/issues/1284)'s condition). Its explicit case needs every interface independent of every oracle, so a mix of annotated and inferred members is unproved.
- T3 and T4's explicit and well-founded cases are on `Compiler` (and [`TCompiler`](../packages/inc-comp/IncComp/Tree.lean#L26) for T3). On [`XCompiler`](../packages/inc-comp/IncComp/General.lean#L22) only the explicit T3b exists, inside `BinCompat`.
- `comp` fails for F4, F5 and F6 ([`SplitProof.Spec.joint_not_comp`](../packages/zinc/Zinc/Features/SplitProof.lean#L952), [`ZincBridgeScala3.not_comp`](../packages/links/Links/ZincBridgeScala3.lean#L79)), and wherever a compiler skips a fact in progress instead of forcing it: scalac's implicit search gives one program three outcomes by typing order ([`implicitSkip_separate`](../packages/scala-types/ScalaTypes/Laziness.lean#L253), finding L1 of [`findings.md`](findings.md)). [`forceAll_ok`](../packages/query/Query/Lazy.lean#L160)'s order-independence needs every consumer to force; a consumer that peeks ([`Lazy.forcePeek`](../packages/query/Query/Lazy.lean#L249)) is outside it.
- The set of units is fixed; additions and deletions are absent sources ([`Added.lean`](../packages/zinc/Zinc/Features/Added.lean)).
- T3a covers only runs that return within fuel.
- Precision has no framework definition; it is proved per instance.

## Trust

- No `sorry`, `admit` or `axiom` declarations.
- `native_decide` appears only in `example`s, never in a `theorem` or `lemma`: those are checks on a bounded space, not results ([`specification.md`](specification.md)). [`scripts/lint_native_decide.py`](../scripts/lint_native_decide.py) enforces this over every `.lean` file of every package, in CI.
- [`scripts/Axioms.lean`](../scripts/Axioms.lean) prints the axioms of the core theorems, of the counterexamples proved by `decide`, and of the instances' soundness theorems; [`scripts/check_axioms.py`](../scripts/check_axioms.py) fails unless each uses only `propext`, `Classical.choice` and `Quot.sound` (so no `sorryAx` and no `Lean.ofReduceBool`), in CI.
