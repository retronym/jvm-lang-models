// in dotc's package: the phase table is private[dotc]
package dotty.tools.dotc.phasesprobe

import dotty.tools.dotc.*
import dotty.tools.dotc.core.*
import Contexts.*, Symbols.*, Phases.*, Flags.*, Decorators.*
import ast.tpd.TreeOps
import scala.collection.mutable

/** Scopes in dotc, as `Scopes2` measures scalac: a snapshot phase between phase groups records each
 *  class's declarations as seen at that point of the run; after the run, the same question is asked
 *  again at each snapshot's phase (`atPhase`). dotc installs a new denotation, with its own scope,
 *  when a phase enters or removes members (`enteredAfter`, `installAfter`), so the late answer
 *  should equal the snapshot. Snapshots sit between groups, so they do not split a fused group.
 *
 *  Usage: Scopes3 subject.scala */
object Scopes3 {
  val classes = mutable.LinkedHashMap[String, Symbol]()
  val snap = mutable.LinkedHashMap[(String, String), List[String]]()
  val phases = mutable.LinkedHashMap[String, Phase]()
  var saved: Context | Null = null

  def decls(sym: Symbol)(using Context): List[String] =
    sym.info.decls.toList.map(d => (if d.isClass then "cla " else if d.is(Method) then "met " else "val ") + d.name.toString)

  class Snapshot(after: String) extends Phase {
    def phaseName = "snap-" + after
    protected def run(using Context): Unit = {
      saved = ctx
      phases(after) = ctx.phase
      if (after == "typer") ctx.compilationUnit.tpdTree.foreachSubTree {
        case t: ast.tpd.TypeDef if t.symbol.isClass =>
          classes(t.symbol.showFullName + (if t.symbol.is(ModuleClass) then "$" else "")) = t.symbol
        case _ =>
      }
      for ((name, sym) <- classes) snap((name, after)) = decls(sym)
    }
  }

  class Comp extends Compiler {
    val after = List("typer", "posttyper", "pickler", "inlining", "firstTransform", "erasure", "mixin", "lambdaLift", "restoreScopes")
    override def phases: List[List[Phase]] =
      super.phases.flatMap { group =>
        after.find(n => group.exists(_.phaseName == n)) match
          case Some(n) => List(group, List(new Snapshot(n)))
          case None => List(group)
      }
  }

  def main(args: Array[String]): Unit = {
    val driver = new Driver { override def newCompiler(using Context): Compiler = new Comp }
    val out = java.nio.file.Files.createTempDirectory("scopes3").toString
    driver.process(Array("-usejavacp", "-color:never", "-d", out) ++ args)
    given Context = saved.nn
    var changed = 0
    for ((name, sym) <- classes) {
      println(s"== $name")
      for ((after, ph) <- phases) {
        val during = snap.getOrElse((name, after), Nil)
        val late = atPhase(ph)(decls(sym))
        val added = late.filterNot(during.contains)
        val gone = during.filterNot(late.contains)
        if (added.nonEmpty || gone.nonEmpty) {
          changed += 1
          println(f"  $after%-14s after the run, added: ${added.mkString(", ")}" + (if (gone.nonEmpty) s"; removed: ${gone.mkString(", ")}" else ""))
        }
      }
    }
    println(s"${classes.size} classes, ${phases.size} phases: $changed (class, phase) answers changed after the run")
  }
}
