// expect: ok ok ok
// kind: ok
// the parent is a class in the companion
class C extends C.P
object C { class P }
