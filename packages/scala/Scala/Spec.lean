import Scala.Lower

/-!
# `Scala`: the specification at a glance

What scalac and dotc emit for a Scala subset: lowering to classfiles as a `Query.Task`, with
forwarders, bridges, `$init$` calls and erasure.

* `Scala.lower_congr`: an edit outside a unit's trace leaves its classfiles unchanged; the hook to
  `IncComp.XCompiler` and to B4 in `Links`.

Calibrated against scalac 2.12.21 and 2.13.18 on 1,348 programs and dotc 3.9.0 on 1,363.
-/

/-- The results this page states, as checked names: the build fails if one is renamed or removed. -/
def Scala.spec : List Lean.Name :=
  [``Scala.lower_congr]
