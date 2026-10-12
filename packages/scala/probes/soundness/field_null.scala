// The path's prefix has a field of conflicting type, initialised to null: o.f.L.
package PKG
object Main {
  trait A { type L >: Int }
  trait B { type L <: String }
  class Holder { val f: A AND B = null }
  val o = new Holder
  def up(x: Int): o.f.L = x
  def main(args: Array[String]): Unit = {
    val s: String = up(1)
    println(s.length)
  }
}
