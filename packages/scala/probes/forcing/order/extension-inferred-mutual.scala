// only: 3
// file: E.scala
object E { extension (s: String) def twice = U.k(s) * 2 }
// file: U.scala
object U { import E.*; def k(s: String) = s.length; def m = "ab".twice }
