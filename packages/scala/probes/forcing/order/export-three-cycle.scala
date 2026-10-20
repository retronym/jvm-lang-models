// only: 3
// file: A.scala
object A { export B.*; def a = 1 }
// file: B.scala
object B { export C.c; def b = 2 }
// file: C.scala
object C { export A.a; def c = 3 }
