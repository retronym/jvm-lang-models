import scala.tools.nsc._
import scala.collection.mutable

/** Scopes in scalac. A snapshot phase runs right after every phase of the run and records each
 *  class's declarations at that phase (`exitingPhase(p)(cls.info.decls)`), at the time. After the
 *  run, the same question is asked again for every phase. A member present in the late answer but
 *  not in the snapshot was entered into the class's `Scope` by a later phase: scalac's info
 *  transformers copy a scope only when they change the declarations, and tree transformers enter
 *  members into the scope of the current info, which earlier phases' infos may share.
 *
 *  Usage: Scopes2 [scalac options] subject.scala */
object Scopes2 {
  class G(s: Settings) extends Global(s) {
    val classes = mutable.LinkedHashMap[String, Symbol]()
    /** (class, phase) -> declarations at that phase, as recorded during the run. */
    val snap = mutable.LinkedHashMap[(String, String), List[String]]()
    val observed = mutable.ListBuffer[String]()
    def decls(sym: Symbol): List[String] = sym.info.decls.toList.map(d => d.kindString.take(3) + " " + d.name.decode)

    class Snapshot(after: String) extends SubComponent {
      val global: G.this.type = G.this
      val phaseName = "snap-" + after
      val runsAfter = List(after)
      override val runsRightAfter = Some(after)
      def newPhase(prev: Phase): Phase = new StdPhase(prev) {
        def apply(unit: CompilationUnit): Unit = {
          if (after == "typer") unit.body.foreach {
            case cd: ClassDef => classes(cd.symbol.fullName) = cd.symbol
            case md: ModuleDef => classes(md.symbol.moduleClass.fullName + "$") = md.symbol.moduleClass
            case _ =>
          }
          val ph = currentRun.phaseNamed(after)
          for ((name, sym) <- classes) snap((name, after)) = exitingPhase(ph)(decls(sym))
          if (!observed.contains(after)) observed += after
        }
      }
    }
    // not right after a phase another phase is hard-linked to (scalac's `runsRightAfter`):
    // tailcalls (specialize), explicitouter (erasure), erasure (posterasure)
    val observe = sys.props.get("phases").map(_.split(',').toList).getOrElse(List("typer", "refchecks", "uncurry",
      "fields", "specialize", "posterasure", "lambdalift", "constructors", "flatten", "mixin", "cleanup", "delambdafy"))
    override protected def computeInternalPhases(): Unit = {
      super.computeInternalPhases()
      for (p <- observe) addToPhasesSet(new Snapshot(p), s"snapshot after $p")
    }
  }

  def main(args: Array[String]): Unit = {
    val s = new Settings; s.usejavacp.value = true; s.outputDirs.setSingleOutput(sys.props("java.io.tmpdir"))
    val (_, files) = s.processArguments(args.toList, processAll = true)
    val g = new G(s); import g._
    val run = new Run
    run.compile(files)
    var leaks = 0
    for ((name, sym) <- classes) {
      // phases whose (late) answers are one `Scope` object: an info transformer copied the scope between groups
      val ids = g.observed.toList.map(ph => System.identityHashCode(exitingPhase(run.phaseNamed(ph))(sym.info.decls)))
      val groups = g.observed.toList.zip(ids).foldRight(List.empty[List[String]]) {
        case ((ph, id), (h :: t)) if ids(g.observed.indexOf(h.head)) == id => (ph :: h) :: t
        case ((ph, _), acc) => List(ph) :: acc
      }
      println(s"== $name  scopes: ${groups.map(_.mkString(" ")).mkString(" | ")}")
      for (ph <- g.observed) {
        val during = g.snap.getOrElse((name, ph), Nil)
        val after = exitingPhase(run.phaseNamed(ph))(decls(sym))
        val added = after.filterNot(during.contains)
        val gone = during.filterNot(after.contains)
        if (added.nonEmpty || gone.nonEmpty) {
          leaks += 1
          println(f"  $ph%-14s after the run, added: ${added.mkString(", ")}" + (if (gone.nonEmpty) s"; removed: ${gone.mkString(", ")}" else ""))
        }
      }
    }
    println(s"${g.classes.size} classes, ${g.observed.size} phases: $leaks (class, phase) answers changed after the run")
  }
}
