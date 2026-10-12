// Two views of one path: up through A (L >: Int), down through B (L <: String); the path is a param.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: String }
  def up(a: A)(x: Int): a.L = x
  def down(b: B)(l: b.L): String = l
  def go(p: A AND B): String = down(p)(up(p)(1))
  def main(args: Array[String]): Unit = {
    val s: String = go(null)
    println(s.length)
  }
}
