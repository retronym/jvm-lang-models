// file: O.scala
object O { transparent inline def f = U.g }
// file: U.scala
object U { def g = 1; def h = O.f }
