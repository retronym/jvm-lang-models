// expect: ok ok ok
// kind: ok
// a default argument reads the companion
case class C(x: Int = C.d)
object C { val d = 1 }
