// tests/run/final-fields.scala, minimized: scala/scala3#25108. Scala 2.13 prints `T.f4 0 4`;
// dotc prints `T.f4 -4 4` fused (as shipped) and `T.f4 0 4` with every miniphase in a group of its own.
trait T { val f4: Int = { println("T.f4"); -4 }; println(f4) }
object Test extends T { override val f4 = 4; def main(args: Array[String]) = println(f4) }
