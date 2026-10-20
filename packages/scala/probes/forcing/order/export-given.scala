// only: 3
// file: A.scala
object A { export B.given; given Int = 1 }
// file: B.scala
object B { export A.given; given Long = 2L }
