"""The worlds `lub.py` joins over: a hierarchy (`decls`, in a syntax all three compilers accept), named values
(expressions the client can write), and a note. The first `triples_of` values (default 4) form the triples."""

WORLDS = {
    'traits': dict(
        doc='two traits mixed in opposite orders (the scala/scala#11291 example); names sort against declaration order',
        decls='''
trait Zed
trait Abe
class S extends Zed with Abe
class T extends Abe with Zed
class V extends Zed with Abe
object H { def s: S = new S; def t: T = new T; def v: V = new V }
''',
        values={'s': 'H.s', 't': 'H.t', 'v': 'H.v'}),

    'three': dict(
        doc='three traits of equal depth, linearized in three different orders',
        decls='''
trait P1
trait P2
trait P3
class X extends P1 with P2 with P3
class Y extends P3 with P2 with P1
class W extends P2 with P3 with P1
object H { def x: X = new X; def y: Y = new Y; def w: W = new W }
''',
        values={'x': 'H.x', 'y': 'H.y', 'w': 'H.w'}),

    'cases': dict(
        doc='case classes and a case object: Product with Serializable joins a sealed parent',
        decls='''
sealed trait Shape
case class Circle(r: Int) extends Shape
case class Square(s: Int) extends Shape
case object Point extends Shape
case class Other(x: Int)
object H { def ci: Circle = Circle(1); def sq: Square = Square(1); def ot: Other = Other(1) }
''',
        values={'ci': 'H.ci', 'sq': 'H.sq', 'pt': 'Point', 'ot': 'H.ot'}),

    'fbound': dict(
        doc='F-bounded: the join of Fa and Fc is an infinite type, truncated by depth',
        decls='''
trait Fb[T <: Fb[T]]
class Fa extends Fb[Fa]
class Fc extends Fb[Fc]
class Fd extends Fb[Fd]
object H { def a: Fa = new Fa; def c: Fc = new Fc; def d: Fd = new Fd }
''',
        values={'a': 'H.a', 'c': 'H.c', 'd': 'H.d'}),

    'fboundco': dict(
        doc='F-bounded with a covariant parameter: the join is Fb[Fb[...]], truncated by depth',
        decls='''
trait Fb[+T <: Fb[T]]
class Fa extends Fb[Fa]
class Fc extends Fb[Fc]
class Fd extends Fb[Fd]
object H { def a: Fa = new Fa; def c: Fc = new Fc; def d: Fd = new Fd }
''',
        values={'a': 'H.a', 'c': 'H.c', 'd': 'H.d'}),

    'jbox': dict(
        doc='the library F-bounds: String, Integer and Long join to Serializable with Comparable[...]',
        decls='''
object H { def s: String = "s"; def i: java.lang.Integer = java.lang.Integer.valueOf(1); def l: java.lang.Long = java.lang.Long.valueOf(1L) }
''',
        values={'s': 'H.s', 'i': 'H.i', 'l': 'H.l'}),

    'variance': dict(
        doc='a covariant, an invariant and a contravariant constructor applied to Int and String',
        decls='''
class Co[+X]
class Inv[X]
class Contra[-X]
object H { def co1: Co[Int] = new Co; def co2: Co[String] = new Co; def inv1: Inv[Int] = new Inv; def inv2: Inv[String] = new Inv; def ct1: Contra[Int] = new Contra; def ct2: Contra[String] = new Contra }
''',
        values={'co1': 'H.co1', 'co2': 'H.co2', 'inv1': 'H.inv1', 'inv2': 'H.inv2', 'ct1': 'H.ct1', 'ct2': 'H.ct2'},
        triples_of=3),

    'refine': dict(
        doc='members refined in every subclass: scalac adds a refinement to the join, dotc does not',
        decls='''
trait R { def m: Any; def k: Any }
class R1 extends R { def m: Int = 1; def k: Int = 1 }
class R2 extends R { def m: Int = 2; def k: String = "" }
class R3 extends R { def m: String = ""; def k: Int = 1 }
object H { def r1: R1 = new R1; def r2: R2 = new R2; def r3: R3 = new R3 }
''',
        values={'r1': 'H.r1', 'r2': 'H.r2', 'r3': 'H.r3'}),

    'anon': dict(
        doc='anonymous classes with structural members',
        decls='''
trait Q { def m: Any }
object H { def u: Unit = () }
''',
        values={'a1': '(new Q { def m: Int = 1; def x: Int = 1 })', 'a2': '(new Q { def m: Int = 2; def x: Int = 2 })',
                'a3': '(new Q { def m: String = ""; def y: Int = 3 })'}),

    'numeric': dict(
        doc='weak conformance: numeric widening in scalac, literal harmonization in dotc',
        decls='''
object H { val i: Int = 1; val l: Long = 1L; val ch: Char = 'c'; val f: Float = 1.0f; val sh: Short = 1 }
''',
        values={'i': 'H.i', 'l': 'H.l', 'ch': 'H.ch', 'sh': 'H.sh', 'f': 'H.f'},
        triples_of=4),

    'literals': dict(
        doc='constants: literal types are widened in a val, and numeric literals harmonized',
        decls='''
object H { def u: Unit = () }
''',
        values={'one': '1', 'oneL': '1L', 'ch': "'c'", 'str': '"a"'}),

    'singletons': dict(
        doc='objects and stable paths: singleton types in a join',
        decls='''
trait Tr
object O1 extends Tr
object O2 extends Tr
case object C1 extends Tr
object H { val t: Tr = O1 }
''',
        values={'o1': 'O1', 'o2': 'O2', 'c1': 'C1', 'ht': 'H.t'}),

    'alias': dict(
        doc='a type alias and its expansion are equivalent: which one the join keeps depends on order',
        decls='''
trait K
class Kx extends K
object H { type KK = K; def k: K = new Kx; def kk: KK = new Kx; def kx: Kx = new Kx }
''',
        values={'k': 'H.k', 'kk': 'H.kk', 'kx': 'H.kx'}),

    'transparent': dict(
        doc='the join is Product & Serializable, which dotc treats as transparent, so the union is kept and erased by its first operand',
        decls='''
abstract class L extends Product with Serializable
abstract class N extends Serializable with Product
case class L1(i: Int) extends L
case class N1(i: Int) extends N
object H { def l: L = L1(1); def n: N = N1(1); def l1: L1 = L1(1) }
''',
        values={'l': 'H.l', 'n': 'H.n', 'l1': 'H.l1'}),

    'library': dict(
        doc='Option, Either and collections from the library',
        decls='''
object H { def u: Unit = () }
''',
        values={'some': 'Some(1)', 'none': 'None', 'left': 'Left(1)', 'right': 'Right("a")', 'nil': 'Nil', 'vec': 'Vector(1)'},
        triples_of=4),

    'depth': dict(
        doc='a deep base type: the join of classes with a common parent at depth 6',
        decls='''
trait D0
trait D1 extends D0
trait D2 extends D1
trait D3 extends D2
trait D4 extends D3
trait D5 extends D4
class E1 extends D5 { def m: Int = 1 }
class E2 extends D5 { def m: Int = 2 }
class E3 extends D2 { def m: Int = 3 }
object H { def e1: E1 = new E1; def e2: E2 = new E2; def e3: E3 = new E3 }
''',
        values={'e1': 'H.e1', 'e2': 'H.e2', 'e3': 'H.e3'}),
}
