// scala/bug#9633: a null path of type B with A, bounds L <: Nothing and L >: Any.
package PKG
object Main {
  trait A { type L <: Nothing }
  trait B { type L >: Any }
  def toL(b: B)(x: Any): b.L = x
  val p: B AND A = null
  def main(args: Array[String]): Unit = {
    val y: Nothing = toL(p)("hello")
    println(y)
  }
}
