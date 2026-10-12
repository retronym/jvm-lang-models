import Links.ZincBridgeKeys
import Links.ZincBridgeScala3

/-!
# `Links`: the specification at a glance

Theorems that connect layers.

* `IncComp.XCompiler.untouched_eq_clean` (B4): for a front end meeting Zinc's obligations, a unit
  Zinc never recompiles equals the clean build's, so it links against the new library as a fresh
  build does. Zinc-clean implies binary-compatible; the converse fails.
* `Links.ZincBridgeKeys.loop_witness`: with Zinc's actual keys, a witness that they miss a
  forwarder change.
* `Links.ZincBridgeScala3.not_comp`: for Scala 3 under F6, compositionality fails whatever the keys;
  `Links.ZincBridgeScala3.after_eq_fresh_fix`: with retronym/scala3#10, B4 holds.
-/

/-- The results this page states, as checked names: the build fails if one is renamed or removed. -/
def Links.spec : List Lean.Name :=
  [``IncComp.XCompiler.untouched_eq_clean,
   ``Links.ZincBridgeKeys.loop_witness,
   ``Links.ZincBridgeScala3.not_comp,
   ``Links.ZincBridgeScala3.after_eq_fresh_fix]
