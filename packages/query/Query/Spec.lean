import Query.Task
import Query.Interp
import Query.Lazy
import Query.Freeze

/-!
# `Query`: the specification at a glance

A computation that asks questions is a query tree, `Query.Task`: it returns, or asks a query and
continues with a function of the answer. Running it against an oracle gives an output and a trace,
the queries it asked. Every model in this repository is built on it.

* `Query.Task.run_eq_of_trace` (T1): two oracles that agree on every query of a run's trace give
  the same output and the same trace.
* `Query.Task.run_congr`: the output half of T1, the form most proofs use.
* `Query.Task.run_interp`, `Query.Task.trace_interp`: a task run through an interpretation of its
  queries as tasks over another interface (`interp`) is the task run against the interpreted
  oracle, and its trace is each query's interpretation's trace, in order.

Track L, a compiler's symbol table as a lazy evaluator (`Query.Lazy`, `Query.Freeze`):

* `Query.Lazy.force_ok`: if the rules have a ranked fixed point (well-founded definitions), forcing
  any fact from any consistent store returns its value and never black-holes.
* `Query.Lazy.forceAll_ok`: so every order of demands gives the same answers.
* `Query.Lazy.cycle_unranked`: a black hole means no ranking puts the fact below the fuel.
* `Query.Lazy.phase_ranked`: facts indexed by phase, reading no later phase, rank lexicographically.
* `Query.Freeze.guarded_quasi_det`: a pushed fact whose reads freeze it gives every read the whole
  fact, whatever the order, or the run fails; `Query.Freeze.unguarded_diverges`: unguarded, it is
  order-dependent.
-/

/-- The results this page states, as checked names: the build fails if one is renamed or removed. -/
def Query.spec : List Lean.Name :=
  [``Query.Task.run_eq_of_trace,
   ``Query.Task.run_congr,
   ``Query.Task.run_interp,
   ``Query.Task.trace_interp,
   ``Query.Lazy.force_ok,
   ``Query.Lazy.forceAll_ok,
   ``Query.Lazy.cycle_unranked,
   ``Query.Lazy.phase_ranked,
   ``Query.Freeze.guarded_quasi_det,
   ``Query.Freeze.unguarded_diverges]
