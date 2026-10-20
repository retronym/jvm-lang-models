// only: 3
// file: A.scala
object A { export B.*; def a = 1 }
// file: B.scala
object B { export A.*; def b = 2 }
