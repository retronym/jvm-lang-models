// From scala/scala's DeterminismTest.testLambdaLift: a control, expected the same in every order.
// file: a.scala
class a {
  def x = { def local = "x" }
  def y = { def local = "y" }
}
// file: b.scala
class b { def test(): Unit = { new a().y } }
