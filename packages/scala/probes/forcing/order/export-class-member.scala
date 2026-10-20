// only: 3
// file: C.scala
class C { val d = new D; export d.* }
// file: D.scala
class D { def x = 1; def y = new C().x }
