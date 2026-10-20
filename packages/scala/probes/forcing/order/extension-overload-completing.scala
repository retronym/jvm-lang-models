// only: 3
// file: E.scala
object E {
  extension (s: String) def f: Int = 1
  extension (i: Int) def f = U.g
}
// file: U.scala
object U { import E.*; def g = "a".f }
