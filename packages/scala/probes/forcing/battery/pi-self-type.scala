// expect: ok ok ok
// kind: ok
// a self type naming the subclass
trait D { self: C => def y = x }
class C extends D { def x = 1 }
