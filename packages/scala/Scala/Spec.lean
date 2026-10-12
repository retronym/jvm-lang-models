import Scala.Lower

/-!
# `Scala`: the specification at a glance

What scalac and dotc emit for a Scala subset: lowering to classfiles as a `Query.Task`, with
forwarders, bridges, `$init$` calls and erasure.

* `Scala.lower_congr`: an edit outside a unit's trace leaves its classfiles unchanged; the hook to
  `IncComp.XCompiler` and to B4 in `Links`.

Calibrated against scalac 2.12.21 and 2.13.18 on 1,348 programs and dotc 3.9.0 on 1,363.
-/

-- Each name below must exist: the build fails if a result this page states is renamed or removed.
example := @Scala.lower_congr
