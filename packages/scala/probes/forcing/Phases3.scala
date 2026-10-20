// in dotc's package: the phase table is private[dotc]
package dotty.tools.dotc.forcingprobe

import dotty.tools.dotc.*
import dotty.tools.dotc.core.*
import Contexts.*, Symbols.*, Phases.*, Flags.*, Decorators.*
import ast.tpd.TreeOps
import scala.collection.mutable

/** Phase-indexed facts in dotc, as `Phases2` does for scalac: a phase right after typer records
 *  name, owner, flags and info; after the run the same questions are asked at typer and later
 *  phases with `atPhase`. dotc keeps every version of a symbol's denotation, so a typer-phase
 *  answer should not change.
 *
 *  Usage: Phases3 subject.scala */
object Phases3 {
  val subjects = mutable.LinkedHashMap[String, Symbol]()
  val during = mutable.LinkedHashMap[String, String]()
  var saved: Context | Null = null

  def describe(sym: Symbol)(using Context): String =
    s"name=${sym.name} owner=${sym.owner.name} private=${sym.is(Private)} method=${sym.is(Method)} info=${sym.info.show}"

  class Collect extends Phase {
    def phaseName = "collect"
    protected def run(using Context): Unit = {
      saved = ctx
      ctx.compilationUnit.tpdTree.foreachSubTree {
        case t: ast.tpd.MemberDef if t.symbol.exists && !t.symbol.isConstructor =>
          val s = t.symbol
          val key = s"${s.owner.name}.${s.name}"
          if (Set("A.secret", "A.m", "m.L", "A.O", "A.O$", "A.g")(key)) {
            subjects(key) = s
            during(key) = atPhase(ctx.base.typerPhase.next)(describe(s))
          }
        case _ =>
      }
    }
  }

  class Comp extends Compiler {
    override def phases: List[List[Phase]] = {
      val ps = super.phases
      val i = ps.indexWhere(_.exists(_.phaseName == "typer"))
      ps.take(i + 1) ::: List(new Collect) :: ps.drop(i + 1)
    }
  }

  def main(args: Array[String]): Unit = {
    val driver = new Driver { override def newCompiler(using Context): Compiler = new Comp }
    val out = java.nio.file.Files.createTempDirectory("phases3").toString
    driver.process(Array("-usejavacp", "-color:never", "-d", out) ++ args)
    given Context = saved.nn
    val phases = List("typer", "erasure", "lambdaLift", "flatten", "expandPrivate", "genBCode")
      .flatMap(n => ctx.base.phases.find(_.phaseName == n).map(n -> _))
    for ((key, sym) <- subjects) {
      println(s"== $key")
      println(f"  ${"typer, during the run"}%-26s ${during(key)}")
      for ((n, p) <- phases) {
        val d = atPhase(p.next)(describe(sym))
        val mark = if (n == "typer" && d != during(key)) "   <-- changed since typer ran" else ""
        println(f"  ${s"$n, after the run"}%-26s $d$mark")
      }
    }
  }
}
