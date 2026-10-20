// expect: ok ok ok
// kind: ok
// a user apply suppresses the synthetic one: the class asks the companion's names
object C { def apply(x: Int): C = new C(x + 1) }
case class C(x: Int)
