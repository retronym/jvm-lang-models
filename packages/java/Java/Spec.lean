import Java.Lower

/-!
# `Java`: the specification at a glance

What javac emits for a Java subset, as a `Query.Task` over other classes' interfaces, constants
folded (JLS §13.4.9); and JLS chapter 13's rules checked against `Jvm` linkage (`Java.Jls13`).

* `Java.lower_congr`: an edit outside a unit's trace leaves its classfiles unchanged.

Calibrated against javac 17, 21 and 25 on 99 programs.
-/

/-- The results this page states, as checked names: the build fails if one is renamed or removed. -/
def Java.spec : List Lean.Name :=
  [``Java.lower_congr]
