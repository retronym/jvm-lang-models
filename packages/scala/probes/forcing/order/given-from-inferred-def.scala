// only: 3
// file: O.scala
object O {
  given x: Int = 1
  def y = U.z + 1
}
// file: U.scala
object U { import O.given; def z = summon[Int] }
