// expect: ok ok ok
// kind: ok
// an annotation argument reading the annotated method
class ann(x: Any) extends scala.annotation.StaticAnnotation
class C { @ann(m) def m = 1 }
