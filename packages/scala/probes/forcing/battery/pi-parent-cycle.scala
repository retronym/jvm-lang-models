// expect: cycle cycle cycle
// kind: true
// C extends C.P extends C
class C extends C.P
object C { class P extends C }
