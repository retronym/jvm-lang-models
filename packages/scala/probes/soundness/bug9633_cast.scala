// scala/bug#9633, the generic cast: Int to String through a null path.
package PKG
object Main {
  trait A { type L <: Nothing }
  trait B { type L >: Any }
  def toL(b: B)(x: Any): b.L = x
  val p: B AND A = null
  def cast[T, U](x: T): U = toL(p)(x)
  def main(args: Array[String]): Unit = {
    val s: String = cast[Int, String](1)
    println(s.length)
  }
}
