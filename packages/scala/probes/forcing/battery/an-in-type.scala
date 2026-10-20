// expect: cycle cycle cycle
// kind: true
// an annotation inside a type is typed with the type: m's type needs n, n's needs m
class ann(x: Any) extends scala.annotation.StaticAnnotation
class C { def m: Int @ann(n) = 1; def n = m }
