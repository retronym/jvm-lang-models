// Two views of one path: up through A (L >: Int), down through B (L <: String); the path is a field.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: String }
  def up(a: A)(x: Int): a.L = x
  def down(b: B)(l: b.L): String = l
  class Holder { val f: A AND B = null }
  val h = new Holder
  def main(args: Array[String]): Unit = {
    val s: String = down(h.f)(up(h.f)(1))
    println(s.length)
  }
}
