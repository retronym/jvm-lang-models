// expect: cycle cycle cycle
// kind: true
// the parameter type is the singleton type of a value inferred from apply, which needs the parameter type
case class C(x: C.c.type)
object C { val c = apply(1) }
