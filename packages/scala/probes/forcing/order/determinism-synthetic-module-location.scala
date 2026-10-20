// From scala/scala's DeterminismTest.testSyntheticModuleLocationInDecls: a control.
// file: a.scala
object A {
  class C(val a: Any) extends AnyVal
  implicit class I1(a: String)
  implicit class IV(val a: String) extends AnyVal
  case class CC()
}
// file: b.scala
object B {
  // Order here reversed from definition order in A
  A.CC()
  A.IV("")
  A.I1("")
  new A.C("")
}
