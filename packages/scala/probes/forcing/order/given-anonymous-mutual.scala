// only: 3
// file: O.scala
object O {
  given Int = U.z + 1
}
// file: U.scala
object U { import O.given; def z: Int = 1; def w = summon[Int] }
