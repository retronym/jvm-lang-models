// file: T.scala
trait T { def m = new C().m }
// file: C.scala
class C extends T { override def m = 1 }
