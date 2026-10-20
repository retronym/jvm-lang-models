// only: 3
// file: A.scala
object A { export B.b; def a = 1 }
// file: B.scala
object B { export A.a; def b = 2 }
