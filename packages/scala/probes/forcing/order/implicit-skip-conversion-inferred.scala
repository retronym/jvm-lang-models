// file: O.scala
object O {
  implicit def a(s: String): Int = s.length
  implicit def b(s: String) = U.n + 1
}
// file: U.scala
object U { import O._; def n = { val i: Int = "abc"; i } }
