// Two views of one path: up through A (L >: Int), down through B (L <: String); the path is a new.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: String }
  def up(a: A)(x: Int): a.L = x
  def down(b: B)(l: b.L): String = l
  val p = new A with B {}
  def main(args: Array[String]): Unit = {
    val s: String = down(p)(up(p)(1))
    println(s.length)
  }
}
