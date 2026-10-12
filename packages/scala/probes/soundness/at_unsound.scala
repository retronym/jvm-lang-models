// Amin and Tate, OOPSLA 2016, artifact unsound.scala: a local null path with conflicting bounds.
package PKG
object Main {
  trait LowerBound[T] { type M >: T }
  trait UpperBound[U] { type M <: U }
  def coerce[T, U](t: T): U = {
    def upcast(ub: LowerBound[T], t: T): ub.M = t
    val bounded: LowerBound[T] AND UpperBound[U] = null
    upcast(bounded, t)
  }
  def main(args: Array[String]): Unit = {
    val zero: String = coerce[Integer, String](0)
    println(zero)
  }
}
