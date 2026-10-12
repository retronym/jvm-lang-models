// Control: two views of a null path with consistent bounds (L >: Int, L <: Any); accepted, and must run.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: Any }
  def up(a: A)(x: Int): a.L = x
  def down(b: B)(l: b.L): Any = l
  val p: A AND B = null
  def main(args: Array[String]): Unit = {
    val s: Any = down(p)(up(p)(1))
    println(s)
  }
}
