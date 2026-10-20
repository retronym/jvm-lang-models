// expect: ok ok ok
// kind: ok
// an inherited declared type breaks the m/n recursion
trait T { def m: Int }
class C extends T { def m = n; def n = m }
