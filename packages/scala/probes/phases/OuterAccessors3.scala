package dotty.tools.dotc.phasesprobe
import dotty.tools.dotc.*, core.*, Contexts.*, Phases.*, Symbols.*, Flags.*
import transform.CountOuterAccesses.mightBeDropped
import ast.tpd.TreeOps
/** For each outer accessor: `mightBeDropped` as CountOuterAccesses asks it (its group runs at
 *  countOuterAccesses.next) and as DropOuterAccessors asks it, unfused (dropOuterAccessors.next)
 *  and fused (the phase after the last miniphase of its group). */
object OuterAccessors3 {
  var saved: Context | Null = null
  val accs = collection.mutable.ListBuffer[Symbol]()
  class Grab extends Phase {
    def phaseName = "grab"
    protected def run(using Context): Unit = { saved = ctx
      ctx.compilationUnit.tpdTree.foreachSubTree { case t: ast.tpd.DefDef if t.symbol.is(OuterAccessor) => accs += t.symbol; case _ => } }
  }
  def main(args: Array[String]): Unit = {
    var groupEnd: Phase | Null = null
    new Driver { override def newCompiler(using Context) = new Compiler {
      override def phases = super.phases.flatMap(g => if g.exists(_.phaseName == "lambdaLift") then List(g, List(new Grab)) else List(g))
    } }.process(args)
    given Context = saved.nn
    val count = ctx.base.phases.find(_.phaseName == "countOuterAccesses").get.next
    val drop = ctx.base.phases.find(_.phaseName == "dropOuterAccessors").get
    val last = ctx.base.phases.find(_.phaseName == "repeatableAnnotations").get.next
    for (a <- accs) println(s"${a.name} in ${atPhase(count)(a.owner.name)}: Count ${atPhase(count)(mightBeDropped(a))}, Drop unfused ${atPhase(drop.next)(mightBeDropped(a))}, Drop fused ${atPhase(last)(mightBeDropped(a))}  (owner of owner: ${atPhase(drop.next)(a.owner.owner.name)} / ${atPhase(last)(a.owner.owner.name)})")
  }
}
