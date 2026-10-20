// expect: ok ok ok
// kind: ok
// an abstract type bounded through List: guarded
trait T { type A <: List[A] }
