package p
class A {
  private def secret = 1
  def m(x: Int)(y: Int): Int = { class L { def z = secret }; new L().z + x + y }
  object O
  def g[T](t: T): T = t
}
