import scala.tools.nsc._
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._

/** Are scalac's info transformers independent of when they run? An info transformer runs lazily,
 *  the first time a symbol's info is asked at or after its phase. A phase right after pickler
 *  asks, for every class the unit defines and its declarations, the info at later phases (a
 *  phase travel forward, as specialization and the backend do), so those transformers run before
 *  the tree transformers of the phases in between. The output is compared byte for byte with a
 *  normal compile; a difference is a transformer whose result depends on its timing, or a tree
 *  transformer that mutates what an early copy already took (`Scopes.copy_before_entry`).
 *
 *  Usage: Eager2 -Dforce=erasure,flatten,... [-Dkind=name|binary] [-- scalac options --] file... */
object Eager2 {
  class G(s: Settings, targets: List[String]) extends Global(s) {
    object eager extends SubComponent {
      val global: G.this.type = G.this
      val phaseName = "eager"
      val runsAfter = List("pickler")
      val runsRightAfter = None
      def newPhase(prev: Phase): Phase = new StdPhase(prev) {
        def apply(unit: CompilationUnit): Unit = for (t <- targets) {
          val ph = currentRun.phaseNamed(t)
          unit.body.foreach {
            case cd: ImplDef =>
              val cls = if (cd.symbol.isModule) cd.symbol.moduleClass else cd.symbol
              // -Dkind=name: only the flat name at `ph`, as Zinc's `ClassName.flatname` asks it
              // -Dkind=binary: `javaBinaryNameString` at `ph`, which caches its first answer
              if (sys.props.get("kind").contains("name")) enteringPhase(ph.next) { cls.fullName('.') }
              else if (sys.props.get("kind").contains("binary")) enteringPhase(ph) { cls.javaBinaryNameString }
              else exitingPhase(ph) { cls.info.decls.foreach(_.info) }
            case _ =>
          }
        }
      }
    }
    override protected def computeInternalPhases(): Unit = {
      super.computeInternalPhases()
      if (targets.nonEmpty) addToPhasesSet(eager, "force infos at later phases")
    }
  }

  def compile(targets: List[String], opts: List[String], file: String): (Path, Boolean, String) = {
    val out = Files.createTempDirectory("eager")
    val s = new Settings
    s.usejavacp.value = true
    s.processArguments(opts, processAll = true)
    s.outputDirs.setSingleOutput(out.toString)
    val err = new java.io.ByteArrayOutputStream
    val pw = new java.io.PrintWriter(err, true)
    val ok =
      try {
        val g = new G(s, targets) { override lazy val reporter = new reporters.ConsoleReporter(s, Console.in, pw) }
        val run = new g.Run; run.compile(List(file)); !g.reporter.hasErrors
      } catch { case t: Throwable => pw.println(t.toString); false }
    (out, ok, err.toString.linesIterator.take(3).mkString(" / "))
  }

  def files(root: Path): Map[String, Array[Byte]] =
    Files.walk(root).iterator.asScala.filter(Files.isRegularFile(_)).map(p => root.relativize(p).toString -> Files.readAllBytes(p)).toMap

  def main(args: Array[String]): Unit = {
    val targets = sys.props.getOrElse("force", "erasure").split(',').toList
    val (opts, srcs) = args.indexOf("--") match {
      case -1 => (Nil, args.toList)
      case i => val j = args.indexOf("--", i + 1); (args.slice(i + 1, j).toList, args.drop(j + 1).toList)
    }
    var same, differ, oneSided, bothFail = 0
    for ((src, n) <- srcs.zipWithIndex) {
      val (a, okA, errA) = compile(Nil, opts, src)
      val (b, okB, errB) = compile(targets, opts, src)
      if (!okA && !okB) bothFail += 1
      else if (okA != okB) { oneSided += 1; println(s"ONE-SIDED $src normal=$okA eager=$okB: ${if (okA) errB else errA}") }
      else {
        val fa = files(a); val fb = files(b)
        val diff = (fa.keySet ++ fb.keySet).toList.sorted.filter(k => !java.util.Arrays.equals(fa.getOrElse(k, null), fb.getOrElse(k, null)))
        if (diff.isEmpty) same += 1 else { differ += 1; println(s"DIFFER $src: ${diff.mkString(" ")} ($a $b)") }
      }
      if ((n + 1) % 50 == 0) println(s"... ${n + 1}/${srcs.length}: same $same, differ $differ, one-sided $oneSided, both fail $bothFail")
    }
    println(s"${srcs.length} files: same $same, differ $differ, one-sided $oneSided, both fail $bothFail")
  }
}
