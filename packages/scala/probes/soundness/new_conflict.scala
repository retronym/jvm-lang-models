// A path built by new from traits whose bounds conflict: DOT's realizability holds by construction.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: String }
  val o = new A with B {}
  def up(x: Int): o.L = x
  def main(args: Array[String]): Unit = {
    val s: String = up(1)
    println(s.length)
  }
}
