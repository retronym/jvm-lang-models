// expect: cycle cycle cycle
// kind: true
// scalac types C.m against T.m's result type, dotc takes it from T.m; under the SLS (type of the rhs) it would be well-founded
trait T { def m = new C().m }
class C extends T { override def m = 1 }
