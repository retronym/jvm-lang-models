// file: O.scala
object O {
  implicit def a(s: String): Int = s.length
  implicit def b(s: String) = U.n
}
// file: U.scala
object U { import O._; def n: Int = { val i: Int = "abc"; i } }
