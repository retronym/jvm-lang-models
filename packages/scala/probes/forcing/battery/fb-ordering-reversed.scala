// expect: ok ok ok
// kind: ok
// the same, the other order
class C extends Ord[C] { def cmp(a: C) = 0 }
trait Ord[A <: Ord[A]] { def cmp(a: A): Int }
