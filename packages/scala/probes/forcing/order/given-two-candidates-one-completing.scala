// only: 3
// file: O.scala
object O {
  given x: Int = 1
  given y: Long = U.z.toLong
}
// file: U.scala
object U { import O.given; def z = summon[Int] + summon[Long].toInt }
