// scala/scala3#50 with a strict val initialised to null instead of a lazy val.
package PKG
object Main {
  trait A { type X = String }
  trait B { type X = Int }
  val o: A AND B = null
  def xToString(x: o.X): String = x
  def intToString(i: Int): String = xToString(i)
  def main(args: Array[String]): Unit = {
    val s: String = intToString(1)
    println(s.length)
  }
}
