package p
trait T { def t: Int = 1; val tv: Int = 2 }
class A extends T {
  private def secret = 1
  def m(x: Int): Int = { class L { def z = secret }; new L().z + x }
  lazy val lz: Int = 3
  object O
  class Inner { def outer = A.this }
  def f = (i: Int) => i + 1
}
object A { def make = new A }
