// expect: cycle cycle cycle
// kind: true
// y needs k needs y, through copy
case class C(x: Int) { def y = C.k }
object C { def k = C(1).copy(x = 2).y }
