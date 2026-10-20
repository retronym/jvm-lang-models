// expect: ok ok ok
// kind: ok
// a parameter type from the companion: the companion's members, not the class's
case class C(x: C.T)
object C { type T = Int }
