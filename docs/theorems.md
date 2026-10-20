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

## Where the hypotheses bite

- Abstraction is perfect hashing: collisions of Zinc's 32-bit name hashes are excluded by fiat.
- T3's well-founded case covers every traced query under every oracle, which rules out self-queries and body-level cycles; uniqueness should need only that the dependencies affecting interfaces are well-founded ([sbt/zinc#1284](https://github.com/sbt/zinc/issues/1284)'s condition). Its explicit case needs every interface independent of every oracle, so a mix of annotated and inferred members is unproved.
- T3 and T4's explicit and well-founded cases are on `Compiler` (and [`TCompiler`](../packages/inc-comp/IncComp/Tree.lean#L26) for T3). On [`XCompiler`](../packages/inc-comp/IncComp/General.lean#L22) only the explicit T3b exists, inside `BinCompat`.
- `comp` fails for F4, F5 and F6 ([`SplitProof.Spec.joint_not_comp`](../packages/zinc/Zinc/Features/SplitProof.lean#L952), [`ZincBridgeScala3.not_comp`](../packages/links/Links/ZincBridgeScala3.lean#L79)), and wherever a compiler skips a fact in progress instead of forcing it: scalac's implicit search gives one program three outcomes by typing order ([`implicitSkip_separate`](../packages/scala-types/ScalaTypes/Laziness.lean#L252), finding L1 of [`findings.md`](findings.md)). [`forceAll_ok`](../packages/query/Query/Lazy.lean#L160)'s order-independence needs every consumer to force; a consumer that peeks ([`Lazy.forcePeek`](../packages/query/Query/Lazy.lean#L249)) is outside it.
- The set of units is fixed; additions and deletions are absent sources ([`Added.lean`](../packages/zinc/Zinc/Features/Added.lean)).
- T3a covers only runs that return within fuel.
- Precision has no framework definition; it is proved per instance.

## Trust

- No `sorry`, `admit` or `axiom` declarations.
- `native_decide` appears only in `example`s, never in a `theorem` or `lemma`: those are checks on a bounded space, not results ([`specification.md`](specification.md)). [`scripts/lint_native_decide.py`](../scripts/lint_native_decide.py) enforces this over every `.lean` file of every package, in CI.
- [`scripts/Axioms.lean`](../scripts/Axioms.lean) prints the axioms of the core theorems, of the counterexamples proved by `decide`, and of the instances' soundness theorems; [`scripts/check_axioms.py`](../scripts/check_axioms.py) fails unless each uses only `propext`, `Classical.choice` and `Quot.sound` (so no `sorryAx` and no `Lean.ofReduceBool`), in CI.
