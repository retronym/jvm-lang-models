// expect: ok ok ok
// kind: ok
// annotations on definitions are typed lazily
@deprecated(C.msg, "") class C
object C { final val msg = "x" }
