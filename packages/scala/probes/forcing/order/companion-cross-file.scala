// file: C.scala
case class C(x: Int = D.d)
// file: D.scala
object D { def d = C().x + 1 }
