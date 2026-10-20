import scala.tools.nsc._
import scala.collection.mutable

/** Phase-indexed facts in scalac: a symbol's name, owner, flags and info, asked at a phase.
 *
 *  A phase right after typer records what typer sees. After the run, the same typer-phase
 *  questions are asked again, and the facts are asked at later phases. A fact whose typer-phase
 *  answer changed was overwritten by a later phase instead of being indexed by phase.
 *
 *  Usage: Phases2 subject.scala */
object Phases2 {
  class G(s: Settings) extends Global(s) {
    val subjects = mutable.LinkedHashMap[String, Symbol]()
    val during = mutable.LinkedHashMap[String, String]()
    def describe(sym: Symbol): String =
      s"name=${sym.name} owner=${sym.owner.name} private=${sym.isPrivate} method=${sym.isMethod}"
    object collector extends SubComponent {
      val global: G.this.type = G.this
      val phaseName = "collect"
      val runsAfter = List("typer")
      override val runsRightAfter = Some("typer")
      def newPhase(prev: Phase): Phase = new StdPhase(prev) {
        def apply(unit: CompilationUnit): Unit = unit.body.foreach { t =>
          if (t.isDef && t.symbol != null && t.symbol != NoSymbol && !t.symbol.isConstructor) {
            val s = t.symbol
            val key = s"${s.owner.name}.${s.name}"
            if (Set("A.secret", "A.m", "m.L", "A.O", "A.g")(key)) {
              subjects(key) = s
              during(key) = exitingTyper(describe(s) + s" info=${s.info}")
            }
          }
        }
      }
    }
    override protected def computeInternalPhases(): Unit = {
      super.computeInternalPhases()
      addToPhasesSet(collector, "record what typer sees")
    }
  }

  def main(args: Array[String]): Unit = {
    val s = new Settings; s.usejavacp.value = true; s.outputDirs.setSingleOutput(sys.props("java.io.tmpdir"))
    val g = new G(s); import g._
    val run = new Run
    run.compile(args.toList)
    val phases = List("typer", "uncurry", "explicitouter", "erasure", "lambdalift", "flatten", "jvm")
      .filter(run.phaseNamed(_) != NoPhase)
    for ((key, sym) <- subjects) {
      println(s"== $key")
      println(f"  ${"typer, during the run"}%-26s ${during(key)}")
      for (ph <- phases) {
        val p = run.phaseNamed(ph)
        val d = exitingPhase(p)(describe(sym) + s" info=${sym.info}")
        val mark = if (ph == "typer" && d != during(key)) "   <-- changed since typer ran" else ""
        println(f"  ${s"$ph, after the run"}%-26s $d$mark")
      }
    }
  }
}
