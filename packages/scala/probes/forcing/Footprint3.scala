// in dotc's package, like Phases3
package dotty.tools.dotc.forcingprobe

import dotty.tools.dotc.*
import dotty.tools.dotc.core.*
import Contexts.*, Symbols.*, Types.*, Flags.*, Names.*, Phases.*, Scopes.*, SymDenotations.*
import scala.collection.mutable

/** Forcing footprints in dotc: symbols whose infos are spy completers, and which of them each
 *  operation forces, cold and from inside a completer. The same menu as `Footprint2` (scalac).
 *
 *  Usage: Footprint3 (compiles a one-line file to get a context, then probes at typer) */
object Footprint3 {
  val log = mutable.ArrayBuffer[String]()
  var saved: Context | Null = null

  class Save extends Phase {
    def phaseName = "save"
    protected def run(using Context): Unit = saved = ctx
  }
  class Comp extends Compiler {
    override def phases: List[List[Phase]] = {
      val ps = super.phases
      val i = ps.indexWhere(_.exists(_.phaseName == "typer"))
      ps.take(i + 1) ::: List(new Save) :: ps.drop(i + 1)
    }
  }

  def spy(name: String)(body: Symbol => Context ?=> Type): LazyType = new LazyType {
    def complete(denot: SymDenotation)(using Context): Unit = { log += name; denot.info = body(denot.symbol) }
  }

  var fresh = 0
  /** class A_k { def m: Int; def n: Int }; `hook` runs inside n's completer, `clsHook` inside A's. */
  def mk(hook: (ClassSymbol, Symbol) => Context ?=> Unit = (_, _) => (),
         clsHook: ClassSymbol => Context ?=> Unit = _ => ())(using Context): (ClassSymbol, Symbol, Symbol) = {
    fresh += 1
    val pkg = defn.EmptyPackageClass
    var mm: Symbol = NoSymbol
    val cls = newClassSymbol(pkg, typeName(s"A$fresh"), EmptyFlags, cls => spy("A") { _ =>
      clsHook(cls)
      val decls = newScope
      val m = newSymbol(cls, termName("m"), Method, spy("m")(_ => ExprType(defn.IntType)))
      mm = m
      val n = newSymbol(cls, termName("n"), Method, spy("n") { _ => hook(cls, m); ExprType(defn.IntType) })
      decls.enter(m); decls.enter(n)
      ClassInfo(pkg.thisType, cls, List(defn.ObjectType), decls)
    })
    pkg.info.decls.openForMutations.enter(cls)
    (cls, NoSymbol, NoSymbol)
  }
  def m(cls: ClassSymbol)(using Context) = cls.info.decl(termName("m")).symbol
  def n(cls: ClassSymbol)(using Context) = cls.info.decl(termName("n")).symbol

  def attempt(f: => Any): String =
    try { f; "ok" } catch { case e: Throwable => s"!! ${e.getClass.getSimpleName}" }

  def main(args: Array[String]): Unit = {
    val f = java.nio.file.Files.createTempFile("footprint", ".scala")
    java.nio.file.Files.writeString(f, "object Dummy\n")
    val out = java.nio.file.Files.createTempDirectory("footprint3").toString
    val driver = new Driver { override def newCompiler(using Context): Compiler = new Comp }
    driver.process(Array("-usejavacp", "-color:never", "-d", out, f.toString))
    given Context = saved.nn
    def probe(label: String)(op: ClassSymbol => Context ?=> Any): Unit = {
      val (cls, _, _) = mk(); log.clear()
      val r = attempt(op(cls))
      println(f"cold:              $label%-30s forced: ${log.mkString(", ")}%-8s $r")
    }
    def reenter(label: String)(h: ClassSymbol => Context ?=> Any): Unit = {
      var r = ""
      val (cls, _, _) = mk(hook = (c, _) => r = attempt(h(c))); log.clear()
      attempt(n(cls).info)
      println(f"in n's completer:  $label%-30s forced: ${log.mkString(", ")}%-8s $r")
    }
    def inClass(label: String)(h: ClassSymbol => Context ?=> Any): Unit = {
      var r = ""
      val (cls, _, _) = mk(clsHook = c => r = attempt(h(c))); log.clear()
      attempt(cls.info)
      println(f"in A's completer:  $label%-30s forced: ${log.mkString(", ")}%-8s $r")
    }
    probe("A.typeRef")(_.typeRef)
    probe("A.is(Trait) (AfterLoadFlags)")(_.is(Trait))
    probe("A.is(Stable) (not known)")(_.is(StableRealizable))
    probe("A.info")(_.info)
    probe("A.info.decl(m)")(_.info.decl(termName("m")))
    probe("A.info.member(m)")(_.info.member(termName("m")))
    probe("A.info.member(m).info")(_.info.member(termName("m")).info)
    probe("A.info.decls")(_.info.decls.toList)
    probe("A.baseClasses")(_.baseClasses)
    probe("A.typeRef <:< AnyRef")(_.typeRef <:< defn.AnyRefType)
    probe("erasure(A.typeRef)")(c => TypeErasure.erasure(c.typeRef))
    reenter("A.info.member(m).info")(_.info.member(termName("m")).info)
    reenter("A.info.member(n).info")(_.info.member(termName("n")).info)
    reenter("A.info.decls.map(info)")(_.info.decls.toList.map(_.info))
    reenter("A.baseClasses")(_.baseClasses)
    inClass("A.typeRef")(_.typeRef)
    inClass("A.is(Trait) (AfterLoadFlags)")(_.is(Trait))
    inClass("A.is(Stable) (not known)")(_.is(StableRealizable))
    inClass("A.typeParams")(_.typeParams)
    inClass("A.info")(_.info)
    inClass("A.baseClasses")(_.baseClasses)
  }
}
