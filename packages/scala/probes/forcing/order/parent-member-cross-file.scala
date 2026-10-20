// file: B.scala
trait B[A <: B[A]]
// file: C.scala
class C extends B[C#T] { type T = C }
