// expect: cycle cycle cycle
// kind: true
// a type parameter bounded by itself
class C[A <: A]
