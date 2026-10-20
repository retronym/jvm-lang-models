// expect: cycle cycle ok
// kind: spurious
// the parent reads C#T, an alias needing only C by name; scalac completes parents and members as one info, dotc publishes the members first (TempClassInfo)
trait B[A <: B[A]]
class C extends B[C#T] { type T = C }
