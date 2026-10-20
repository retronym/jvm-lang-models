// file: O.scala
object O {
  implicit val x: Int = 1
  implicit def y: Int = U.z + 1
}
// file: U.scala
object U { import O._; def z = implicitly[Int] }
