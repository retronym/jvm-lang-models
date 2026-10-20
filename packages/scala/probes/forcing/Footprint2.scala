import scala.tools.nsc._
import scala.collection.mutable

/** Forcing footprints in scalac: symbols whose infos are spy completers, and which of them each
 *  operation forces, cold and from inside a completer. The same menu as `Footprint3` (dotc).
 *
 *  Usage: Footprint2 */
object Footprint2 {
  def main(args: Array[String]): Unit = {
    val s = new Settings; s.usejavacp.value = true
    val g = new Global(s); import g._
    new Run
    val log = mutable.ArrayBuffer[String]()
    def spy(name: String)(body: Symbol => Type) = new LazyType {
      override def complete(sym: Symbol): Unit = { log += name; sym.setInfo(body(sym)) }
    }
    var fresh = 0
    /** class A_k { def m: Int; def n: Int }; `hook` runs inside n's completer, `clsHook` inside A's. */
    def mk(hook: Symbol => Unit = _ => (), clsHook: Symbol => Unit = _ => ()): Symbol = {
      fresh += 1
      val pkg = rootMirror.EmptyPackageClass
      val A = pkg.newClassSymbol(TypeName(s"A$fresh"))
      A.setInfo(spy("A") { cls =>
        clsHook(cls)
        val decls = newScope
        val m = cls.newMethod(TermName("m")); val n = cls.newMethod(TermName("n"))
        m.setInfo(spy("m")(_ => NullaryMethodType(definitions.IntTpe)))
        n.setInfo(spy("n") { _ => hook(cls); NullaryMethodType(definitions.IntTpe) })
        decls.enter(m); decls.enter(n)
        ClassInfoType(List(definitions.AnyRefTpe), decls, cls)
      })
      pkg.info.decls.enter(A)
      A
    }
    def attempt(f: => Any): String =
      try { f; "ok" } catch { case e: Throwable => s"!! ${e.getClass.getSimpleName}" }
    def probe(label: String)(op: Symbol => Any): Unit = {
      val a = mk(); log.clear()
      val r = attempt(op(a))
      println(f"cold:              $label%-30s forced: ${log.mkString(", ")}%-8s $r")
    }
    def reenter(label: String)(h: Symbol => Any): Unit = {
      var r = ""
      val a = mk(hook = c => r = attempt(h(c))); log.clear()
      attempt(a.info.decl(TermName("n")).info)
      println(f"in n's completer:  $label%-30s forced: ${log.mkString(", ")}%-8s $r")
    }
    def inClass(label: String)(h: Symbol => Any): Unit = {
      var r = ""
      val a = mk(clsHook = c => r = attempt(h(c))); log.clear()
      attempt(a.info)
      println(f"in A's completer:  $label%-30s forced: ${log.mkString(", ")}%-8s $r")
    }
    enteringTyper {
      probe("A.typeRef")(_.typeConstructor)
      probe("A.isTrait")(_.isTrait)
      probe("A.isStable")(_.isStable)
      probe("A.info")(_.info)
      probe("A.info.decl(m)")(_.info.decl(TermName("m")))
      probe("A.info.member(m)")(_.info.member(TermName("m")))
      probe("A.info.member(m).info")(_.info.member(TermName("m")).info)
      probe("A.info.decls")(_.info.decls.toList)
      probe("A.baseClasses")(_.tpe_*.baseClasses)
      probe("A.typeRef <:< AnyRef")(_.tpe_* <:< definitions.AnyRefTpe)
      probe("erasure(A.typeRef)")(a => erasure.erasure(a)(a.tpe_*))
      reenter("A.info.member(m).info")(_.info.member(TermName("m")).info)
      reenter("A.info.member(n).info")(_.info.member(TermName("n")).info)
      reenter("A.info.decls.map(info)")(_.info.decls.toList.map(_.info))
      reenter("A.baseClasses")(_.tpe_*.baseClasses)
      inClass("A.typeRef")(_.typeConstructor)
      inClass("A.isTrait")(_.isTrait)
      inClass("A.isStable")(_.isStable)
      inClass("A.typeParams")(_.typeParams)
      inClass("A.info")(_.info)
      inClass("A.baseClasses")(_.tpe_*.baseClasses)
    }
  }
}
