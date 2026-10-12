// scala/scala3#50: a lazy val path, never forced, of type A & B with X = String and X = Int.
package PKG
object Main {
  trait A { type X = String }
  trait B { type X = Int }
  lazy val o: A AND B = ???
  def xToString(x: o.X): String = x
  def intToString(i: Int): String = xToString(i)
  def main(args: Array[String]): Unit = {
    val s: String = intToString(1)
    println(s.length)
  }
}
