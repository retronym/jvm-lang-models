// expect: cycle ok ok
// kind: spurious
// a parent's type argument is an alias in the companion naming the class; fixed between 2.12 and 2.13
class C extends java.lang.Comparable[C.T] { def compareTo(o: C.T) = 0 }
object C { type T = C }
