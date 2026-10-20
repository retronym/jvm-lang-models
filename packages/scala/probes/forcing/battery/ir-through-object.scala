// expect: ok ok ok
// kind: ok
// the parent declares the type
trait T { def m: Int = 0 }
class C extends T { override def m = D.k }
object D { def k = new C().m }
