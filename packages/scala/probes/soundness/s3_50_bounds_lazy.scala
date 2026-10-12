// scala/scala3#50's shape with bounds instead of aliases: a lazy val path, L >: Int and L <: String.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: String }
  lazy val o: A AND B = ???
  def up(x: Int): o.L = x
  def main(args: Array[String]): Unit = {
    val s: String = up(1)
    println(s.length)
  }
}
