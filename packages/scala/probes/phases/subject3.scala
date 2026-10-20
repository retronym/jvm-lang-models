package p
import scala.annotation.{static, unroll}
class F extends (Int => Int) { def apply(i: Int): Int = i + 1 }          // SpecializeFunctions
class S; object S { @static val t: Int = 2 }   // MoveStatics
final class U { def f(a: Int, @unroll b: Int = 0): Int = a + b }               // UnrollDefinitions
enum E extends java.lang.Enum[E] { case X, Y }                           // CompleteJavaEnums
class P { protected def pr = 1; class I { inline def g = pr } }          // AccessProxies (inline accessor)
object O                                                                 // SyntheticMembers: writeReplace
