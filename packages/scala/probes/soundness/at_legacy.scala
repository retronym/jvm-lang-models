// Amin and Tate, artifact legacy.scala: no dependent method types; the null path is a final val field.
package PKG
object Main {
  trait LowerBound[T] { type M >: T }
  trait UpperBound[U] { type M <: U }
  trait Upcast[T] {
    type X <: LowerBound[T]
    def compute: X
    final val ub: X = compute
    def upcast(t: T): ub.M = t
  }
  class Coerce[T, U] extends Upcast[T] {
    type X = LowerBound[T] AND UpperBound[U]
    override def compute = null
    def coerce(t: T): U = upcast(t)
  }
  def main(args: Array[String]): Unit = {
    val zero: String = (new Coerce[Int, String]).coerce(0)
    println(zero)
  }
}
