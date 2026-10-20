// file: O.scala
object O {
  def f(x: Int) = U.g + 1
  def f(x: String): Int = 0
}
// file: U.scala
object U { def g = O.f("s") }
