// The path is a method parameter, passed null.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: String }
  def f(p: A AND B)(x: Int): String = { val l: p.L = x; l }
  def main(args: Array[String]): Unit = {
    val s: String = f(null)(1)
    println(s.length)
  }
}
