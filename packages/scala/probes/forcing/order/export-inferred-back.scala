// only: 3
// file: A.scala
object A { export B.b; def a = b + 1 }
// file: B.scala
object B { def b = 2; def c = A.a }
