# `Query`

A computation that asks questions: a query tree (`Task`) that either returns or asks a query and continues with a function of the answer; running it against an oracle gives the output and the *trace*. T1 ([`Task.run_eq_of_trace`](Query/Task.lean#L40)): two oracles that agree on the trace give the same output. Every model in this repository is built on it. No Mathlib.

**Start here.** [`Query/Task.lean`](Query/Task.lean).

**Calibration.** None needed: it is the free monad of *Build Systems à la Carte* with a dependent answer type.

**Gaps.** None specific.

## Files

| File | Contents |
|---|---|
| [`Task.lean`](Query/Task.lean) | Free monad of query trees; `run`, `trace`; T1 [`run_eq_of_trace`](Query/Task.lean#L40), [`run_congr`](Query/Task.lean#L79) |
| [`Basic.lean`](Query/Basic.lean) | What the Mathlib-free layers took from Mathlib: decidable equality of `Except`, a low-priority `List` monad, `dedupLast` (Mathlib's `dedup`, structural) |
