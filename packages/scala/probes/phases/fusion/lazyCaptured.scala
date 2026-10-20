object Z {
  def m(): Int = { lazy val x = { println("init"); 1 }; val f = () => x; f() + f() }
  def n(): Int = { object Loc { val y = 2 }; val f = () => Loc.y; f() }
  def main(args: Array[String]): Unit = println(m() + n())
}
