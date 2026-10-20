// expect: cycle cycle ok
// kind: spurious
// a refinement of C in its own parent; scalac 2.13.18 crashes with an uncaught TypeError
class D[A <: D[A]]
class C extends D[C { def x: Int }]
