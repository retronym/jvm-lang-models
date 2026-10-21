# `Query`

A computation that asks questions: a query tree (`Task`) that either returns or asks a query and continues with a function of the answer; running it against an oracle gives the output and the *trace*. T1 ([`Task.run_eq_of_trace`](Query/Task.lean#L40)): two oracles that agree on the trace give the same output. Every model in this repository is built on it. No Mathlib.

**Start here.** [`Query/Task.lean`](Query/Task.lean).

**Calibration.** None needed: it is the free monad of *Build Systems à la Carte* with a dependent answer type.

**Gaps.** None specific.

## Files

| File | Contents |
|---|---|
| [`Task.lean`](Query/Task.lean) | Free monad of query trees; `run`, `trace`; T1 [`run_eq_of_trace`](Query/Task.lean#L40), [`run_congr`](Query/Task.lean#L79) |
| [`Interp.lean`](Query/Interp.lean) | A task over one query interface run over another (`interp`, `rename`): [`run_interp`](Query/Interp.lean#L34), [`trace_interp`](Query/Interp.lean#L42) |
| [`Lazy.lean`](Query/Lazy.lean) | Lazy forcing of self-referential facts with black-holing (Track L): with a ranked fixed point it never cycles, in any order ([`force_ok`](Query/Lazy.lean#L111), [`forceAll_ok`](Query/Lazy.lean#L160)); a black hole means no ranking ([`cycle_unranked`](Query/Lazy.lean#L176)); phase-indexed facts rank lexicographically ([`phase_ranked`](Query/Lazy.lean#L199)) |
| [`Freeze.lean`](Query/Freeze.lean) | Facts that grow (a sealed class's children): a read that freezes them makes the answer quasi-deterministic ([`guarded_quasi_det`](Query/Freeze.lean#L67)); without it, order-dependent ([`unguarded_diverges`](Query/Freeze.lean#L105)) |
| [`Interrupt.lean`](Query/Interrupt.lean) | Interrupting the evaluator (Track I): every store a forcing leaves at a safepoint agrees with the semantics, so abort and restart is sound ([`forceA_agree`](Query/Interrupt.lean#L158), [`abort_restart_ok`](Query/Interrupt.lean#L208)), with scalac's and dotc's black-hole disciplines after an abort; nested servicing as a reordering ([`nested_empty_stack_reorders`](Query/Interrupt.lean#L378)) or a spurious cycle; peeking with a taint that keeps the store at the fixed point ([`forceT_agree`](Query/Interrupt.lean#L668)), against `forcePeek` and IntelliJ's rule, which memoize order-dependent answers; the three non-fact shapes of [scala/scala#11328](https://github.com/scala/scala/issues/11328) |
| [`Basic.lean`](Query/Basic.lean) | What the Mathlib-free layers took from Mathlib: decidable equality of `Except`, a low-priority `List` monad, `dedupLast` (Mathlib's `dedup`, structural) |
