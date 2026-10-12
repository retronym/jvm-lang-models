import IncComp.Uniqueness
import IncComp.Termination
import IncComp.Stale
import IncComp.Classpath

/-!
# `IncComp`: the specification at a glance

When does an incremental build equal a clean one, for any compiler and any invalidation policy?

**The compiler and its bridge.** `IncComp.XCompiler`: a per-unit task, joint compilation of a
group, each unit's interface, the answers an interface gives, and the bridge: the keys a unit
records, a hash per key, and which queries a key covers. `IncComp.XCompiler.Obligations` are
compositionality, coverage, abstraction and locality. A policy's one obligation is
`IncComp.Compiler.Policy.Sound`: never drop an invalidated unit outside the round just compiled.

**The theorems, proved once on `XCompiler`.**

* `IncComp.XCompiler.round_preserves` (T2): one round, with the hash diff taken over the affected
  units, preserves the invariant.
* `IncComp.XCompiler.zinc_sound` (T3a): if the loop returns, every unit is up to date.
* `IncComp.XCompiler.zinc_some_of_monotoneFrom` (T4): a policy monotone from round `k`, such as
  `transitiveStep`, returns within `k + |S| + 1` rounds.
* `IncComp.XCompiler.downstream_sound` (T5): a downstream subproject's loop ends sound against the
  new classpath; `IncComp.XCompiler.inv_external` (T5a) needs only abstraction.

**When incremental equals clean**, on the local `Compiler`:

* `IncComp.Compiler.fixpoint_unique_of_wf`, `IncComp.Compiler.fixpoint_unique_of_explicit` (T3b):
  per-unit fixed points are unique under well-founded dependencies, or interfaces that depend on
  the source alone;
* `IncComp.Compiler.zinc_eq_clean_of_wf`, `IncComp.Compiler.zinc_eq_clean_of_explicit` (T3).

**What goes wrong without the right domain.** `IncComp.Stale.stale_unsound`: a non-local hash
diffed over the recompiled units alone undercompiles; `IncComp.Stale.stale_affected`: over the
affected units it does not.
-/

/-- The results this page states, as checked names: the build fails if one is renamed or removed. -/
def IncComp.spec : List Lean.Name :=
  [``IncComp.XCompiler.round_preserves,
   ``IncComp.XCompiler.zinc_sound,
   ``IncComp.XCompiler.zinc_some_of_monotoneFrom,
   ``IncComp.XCompiler.downstream_sound,
   ``IncComp.XCompiler.inv_external,
   ``IncComp.Compiler.fixpoint_unique_of_wf,
   ``IncComp.Compiler.fixpoint_unique_of_explicit,
   ``IncComp.Compiler.zinc_eq_clean_of_wf,
   ``IncComp.Compiler.zinc_eq_clean_of_explicit,
   ``IncComp.Stale.stale_unsound,
   ``IncComp.Stale.stale_affected]
