// in dotc's package: the phase table is private[dotc]
package dotty.tools.dotc.phasesprobe

import dotty.tools.dotc.*
import dotty.tools.dotc.core.*
import Contexts.*, Phases.*
import dotty.tools.dotc.reporting.Reporter
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/** Is MegaPhase fusion transparent? Each source file is compiled twice: with dotc's phase groups,
 *  where the miniphases of a group transform each tree node in turn in one traversal, and with
 *  every miniphase in a group of its own, a traversal each. Fused equals unfused when every pair
 *  of miniphases in a group commutes on the trees they see. The outputs (classfiles and TASTy) are
 *  compared byte for byte; a file that compiles one way and fails the other is reported too.
 *
 *  Usage: Fusion3 [-- dotc options --] file... */
object Fusion3 {
  class Unfused extends Compiler {
    override def phases: List[List[Phase]] = super.phases.flatMap(_.map(List(_)))
  }

  def compile(fused: Boolean, opts: Array[String], file: String): (Path, Boolean, String) = {
    val out = Files.createTempDirectory("fusion")
    val driver = new Driver { override def newCompiler(using Context): Compiler = if fused then new Compiler else new Unfused }
    val err = new java.io.ByteArrayOutputStream
    val reporter = Console.withErr(err)(Console.withOut(err)(
      try driver.process(Array("-usejavacp", "-color:never", "-d", out.toString) ++ opts :+ file)
      catch { case t: Throwable => null }))
    (out, reporter != null && !reporter.hasErrors, err.toString.linesIterator.take(3).mkString(" / "))
  }

  def files(root: Path): Map[String, Array[Byte]] =
    Files.walk(root).iterator.asScala.filter(Files.isRegularFile(_)).map(p => root.relativize(p).toString -> Files.readAllBytes(p)).toMap

  def main(args: Array[String]): Unit = {
    val (opts, srcs) = args.indexOf("--") match
      case -1 => (Array.empty[String], args)
      case i => val j = args.indexOf("--", i + 1); (args.slice(i + 1, j), args.drop(j + 1))
    var same, differ, oneSided, bothFail = 0
    for ((src, n) <- srcs.zipWithIndex) {
      val (a, okA, errA) = compile(fused = true, opts, src)
      val (b, okB, errB) = compile(fused = false, opts, src)
      if (!okA && !okB) bothFail += 1
      else if (okA != okB) { oneSided += 1; println(s"ONE-SIDED $src fused=${okA} unfused=${okB}: ${if okA then errB else errA}") }
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
