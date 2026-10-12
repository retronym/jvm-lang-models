// Control: consistent bounds through a null path; accepted, and must run.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: Any }
  val o: A AND B = null
  def up(x: Int): o.L = x
  def main(args: Array[String]): Unit = {
    val a: Any = up(1)
    println(a)
  }
}
