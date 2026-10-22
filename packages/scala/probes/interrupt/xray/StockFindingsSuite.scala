package dotty.tools.pc.tests.completion

import java.net.URI
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

import scala.concurrent.duration.*
import scala.language.unsafeNulls
import scala.meta.internal.jdk.CollectionConverters.*
import scala.meta.internal.metals.{CompilerOffsetParams, EmptyCancelToken, PcQueryContext}
import scala.meta.internal.pc.PresentationCompilerConfigImpl
import scala.meta.pc.SourcePathMode
import scala.meta.pc.reports.EmptyReportContext

import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.pc.{CachingDriver, ScalaPresentationCompiler}
import dotty.tools.pc.base.BaseCompletionSuite

import org.junit.Test

/** Two behaviours of the STOCK compiler and presentation compiler (this file
 *  runs on an unmodified checkout), found while building the session spike:
 *  a sourcepath member first completed in a run later than the one that
 *  entered it gets `Any` (its Namer completer refuses to run in a later run),
 *  and a `Touched` flag left on a classpath type parameter by a cyclic
 *  reference caught inside the provider's type-ahead survives across requests.
 */
class StockFindingsSuite extends BaseCompletionSuite:

  private val timeout = 60.seconds
  private val sourcepathDir: Path = Files.createDirectories(tmp.resolve("sourcepath"))

  locally:
    val pkg1Dir = Files.createDirectories(sourcepathDir.resolve("pkg1"))
    Files.write(pkg1Dir.resolve("Alpha.scala"),
      """|package pkg1
         |
         |class Alpha:
         |  def greetAlpha = 42
         |  def other(x: Int): Int = x
         |""".stripMargin.getBytes(StandardCharsets.UTF_8))

  override protected def config: PresentationCompilerConfigImpl =
    super.config.copy(sourcePathMode = SourcePathMode.PRUNED, timeoutDelay = 120)
  override protected val sourcePath: Seq[Path] = Seq(sourcepathDir)
  override protected def scalacOptions(classpath: Seq[Path]): Seq[String] = Seq("-Ylogical-package-loading")

  private val uri = URI.create("file:///A.scala")
  private def pc = presentationCompiler.asInstanceOf[ScalaPresentationCompiler]
  private given PcQueryContext = PcQueryContext(None, () => "")(using EmptyReportContext())
  private def withDriver[T](f: CachingDriver => T): T =
    pc.compilerAccess.withNonInterruptableCompiler(null.asInstanceOf[T], EmptyCancelToken)(a => f(a.compiler())).get(timeout.length, timeout.unit)

  private def complete(query: String): String =
    val (code, offset) = params(query)
    presentationCompiler.complete(CompilerOffsetParams(uri, code, offset, EmptyCancelToken)).get(timeout.length, timeout.unit)
      .getItems.asScala.map(_.getLabel).sorted.mkString("\n")

  @Test def `sourcepath-member-first-completed-in-a-later-run` =
    // Run 1 enters Alpha from the sourcepath (its class completes, its members get completers of this run)
    println("[stock I7] first: " + complete("import pkg1.Alpha\nobject Main:\n  val a = new Alpha\n  a.oth@@\n"))
    // Run 2 (different content) first completes greetAlpha, whose completer belongs to run 1
    val second = complete("import pkg1.Alpha\nobject Main:\n  val a = new Alpha\n  val g = a.greetAlpha\n  a.greetA@@\n")
    println("[stock I7] second: " + second)
    val runIds = withDriver(d => d.currentCtx.runId)
    println(s"[stock I7] runId after: $runIds")
    assertNoDiff("greetAlpha: Int", second)

  @Test def `touched-left-on-classpath-type-params-after-a-member-completion` =
    def completing(): List[String] = withDriver { d =>
      given Context = d.currentCtx
      val classes = List("scala.collection.immutable.List", "scala.collection.IterableOnceOps", "scala.collection.IterableOnce",
        "scala.collection.IterableOps", "scala.runtime.RichInt", "scala.collection.StringOps", "scala.collection.StepperShape", "scala.collection.Stepper")
      classes.flatMap { c =>
        val cls = requiredClass(c)
        cls.info.decls.toList.flatMap { m =>
          (m :: m.typeParams).filter(_.isCompleting).map(s => s"$c.${m.name}.${s.name}")
        }
      }
    }
    val before = completing()
    val items = complete("object T {\n  val x = 1.@@\n}\n")
    println(s"[stock I16] completion items: ${items.linesIterator.size}")
    val after = completing()
    println(s"[stock I16] completing before: $before; after: $after")
    val items2 = complete("object T {\n  val y = 2.@@\n}\n")
    println(s"[stock I16] second completion items: ${items2.linesIterator.size}; completing after: ${completing()}")
