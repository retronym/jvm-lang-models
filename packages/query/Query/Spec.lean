import Query.Task

/-!
# `Query`: the specification at a glance

A computation that asks questions is a query tree, `Query.Task`: it returns, or asks a query and
continues with a function of the answer. Running it against an oracle gives an output and a trace,
the queries it asked. Every model in this repository is built on it.

* `Query.Task.run_eq_of_trace` (T1): two oracles that agree on every query of a run's trace give
  the same output and the same trace.
* `Query.Task.run_congr`: the output half of T1, the form most proofs use.
-/

-- Each name below must exist: the build fails if a result this page states is renamed or removed.
example := @Query.Task.run_eq_of_trace
example := @Query.Task.run_congr
