// scala/scala3#1050: projection from an intersection of refinements with contradictory bounds.
package PKG
object Main {
  trait C { type A }
  type T = C { type A >: Any }
  type U = C { type A <: Nothing }
  type X = T AND U
  def main(args: Array[String]): Unit = {
    val y: X#A = 1
    val z: String = y
    println(z.length)
  }
}
