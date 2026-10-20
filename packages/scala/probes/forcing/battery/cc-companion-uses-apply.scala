// expect: ok ok ok
// kind: ok
// the companion calls the synthetic apply, which needs only the constructor's signature
object C { val c = apply(1) }
case class C(x: Int)
