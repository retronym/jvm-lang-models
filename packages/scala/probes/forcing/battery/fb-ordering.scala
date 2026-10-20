// expect: ok ok ok
// kind: ok
// F-bound through the type constructor: guarded
trait Ord[A <: Ord[A]] { def cmp(a: A): Int }
class C extends Ord[C] { def cmp(a: C) = 0 }
