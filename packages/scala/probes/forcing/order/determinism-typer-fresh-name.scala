// From scala/scala's DeterminismTest.testTyperFreshName: a control.
// file: a.scala
class a {
  def x = { { case x if "".isEmpty => "" }: PartialFunction[Any, Any] }
  def y = { { case x if "".isEmpty => "" }: PartialFunction[Any, Any] }
}
// file: b.scala
class b { def test(): Unit = { new a().y } }
