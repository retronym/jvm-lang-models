package dotty.tools.pc.xray

import java.io.File
import java.net.{InetSocketAddress, URI}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import scala.language.unsafeNulls

import com.sun.net.httpserver.{HttpExchange, HttpServer}

import dotty.tools.dotc.{CompilationUnit, Run}
import dotty.tools.dotc.ast.{tpd, untpd}
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Phases
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.interactive.{CachedLogicalPackage, Completion, InteractiveDriver}
import dotty.tools.dotc.parsing.Parsers
import dotty.tools.dotc.util.{SourceFile, SourcePosition}
import dotty.tools.dotc.util.Spans.Span
import dotty.tools.pc.tests.buildinfo.BuildInfo

/** A toy IDE over the patched `InteractiveDriver` (targeted typing, resumable
 *  runs, cancellation that unwinds): one page, one virtual file `A.scala`,
 *  and an x-ray of what the driver did for each request. Every number in the
 *  x-ray is read from the driver; nothing is simulated.
 *
 *  Run from the scala3 worktree with the session patch applied:
 *    sbt --mem 8192 "scala3-presentation-compiler/Test/runMain dotty.tools.pc.xray.XrayServer"
 *  then open http://127.0.0.1:8791/ (`-Dxray.port` to change).
 */
object XrayServer:

  val uri: URI = URI.create("file:///A.scala")
  val objectCount = 60

  /** The same shape as `CompletionSessionSuite.bigSource`, without the marker. */
  def generatedSource(tag: String, n: Int = objectCount): String =
    val objects = (0 until n).map { i =>
      s"""|object M$i {
          |  def method$i(xs: List[Int]): Int = xs.map(_ + $i).filter(_ > $i).sum
          |  val r = this.meth
          |}""".stripMargin
    }.mkString("\n")
    s"// $tag\n$objects\n"

  private val settings =
    List("-color:never", "-Ximport-suggestion-timeout", "0",
      "-classpath", BuildInfo.ideTestsDependencyClasspath.map(_.toPath.toString).mkString(File.pathSeparator))

  private val driver = new InteractiveDriver(settings, CachedLogicalPackage.none)

  /** `Run.typedTreeCount` is private to the compiler; read it reflectively so
   *  that the compiler patch stays exactly `docs/upstream/dotc-session.patch`.
   */
  private val typedTreeCountField =
    classOf[Run].getDeclaredFields.find(_.getName.contains("typedTreeCount")).map { f => f.setAccessible(true); f }
  private def typedTreeCount(run: Run): Int =
    typedTreeCountField.map(_.getInt(run)).getOrElse(-1)

  case class Stat(name: String, start: Int, end: Int)

  /** The top-level statements of `source`, by a parse of their own. */
  private def statements(source: SourceFile): List[Stat] =
    given Context = driver.currentCtx.fresh.setSource(source)
    val tree = new Parsers.Parser(source).parse()
    val stats = tree match
      case untpd.PackageDef(_, stats) => stats
      case _ => Nil
    stats.map { s =>
      val name = s match
        case m: untpd.ModuleDef => s"object ${m.name}"
        case t: untpd.TypeDef => s"${if t.mods.is(dotty.tools.dotc.core.Flags.Trait) then "trait" else "class"} ${t.name}"
        case d: untpd.DefDef => s"def ${d.name}"
        case v: untpd.ValDef => s"val ${v.name}"
        case other => other.getClass.getSimpleName
      Stat(name, s.span.start, s.span.end)
    }

  /** The spans of the typed statements of the current unit of `uri`, if that
   *  unit is for `source` (after an aborted fresh run the previous unit stays
   *  current, and must not be read as typed state of the new content).
   */
  private def typedSpans(source: SourceFile): List[Span] =
    driver.compilationUnits.get(uri) match
      case Some(unit) if unit.source.textContent() == source.textContent() =>
        unit.tpdTree match
          case tpd.PackageDef(_, stats) => stats.map(_.span)
          case _ => Nil
      case _ => Nil

  private def isTyped(stat: Stat, spans: List[Span]): Boolean =
    spans.exists(sp => sp.exists && sp.start <= stat.start && stat.end <= sp.end)

  /** Symbols of this file in the empty package's scope: how many have `Touched`
   *  set without being completed (`isCompleting`), and how many are completed.
   */
  private def scopeCounts(): (Int, Int, Int) =
    given Context = driver.currentCtx
    val pkg = defn.EmptyPackageClass
    val file = driver.openedFiles.get(uri).map(_.file)
    val syms = pkg.info.decls.toList.filter(s => file.exists(f => s.associatedFile != null && s.associatedFile.path == f.path))
    (syms.count(_.isCompleting), syms.count(_.isCompleted), syms.size)

  private val sb = new StringBuilder

  private def jsonStr(s: String): String =
    val b = new StringBuilder("\"")
    s.foreach {
      case '"' => b.append("\\\"")
      case '\\' => b.append("\\\\")
      case '\n' => b.append("\\n")
      case '\r' => b.append("\\r")
      case '\t' => b.append("\\t")
      case c if c < ' ' => b.append(f"\\u${c.toInt}%04x")
      case c => b.append(c)
    }
    b.append('"').toString

  private def json(v: Any): String = v match
    case null => "null"
    case s: String => jsonStr(s)
    case b: Boolean => b.toString
    case n: Int => n.toString
    case n: Long => n.toString
    case n: Double => n.toString
    case m: Map[?, ?] => m.map((k, v) => jsonStr(k.toString) + ":" + json(v)).mkString("{", ",", "}")
    case xs: Seq[?] => xs.map(json).mkString("[", ",", "]")
    case other => jsonStr(other.toString)

  private val lock = new Object

  /** One request against the driver, with its x-ray. `kind` is `complete`
   *  (`runUpTo` at `offset`, then the completions there) or `full` (`run`);
   *  `cancelAfterMs >= 0` installs a cancel checker that fires that long after
   *  the request started.
   */
  def request(kind: String, code: String, offset: Int, cancelAfterMs: Long): Map[String, Any] = lock.synchronized {
    val source = SourceFile.virtual(uri, code)
    val stats = statements(source)
    val typedBefore = typedSpans(source)
    val runIdBefore = driver.currentCtx.runId
    val sessionRunBefore = driver.runIdOf(uri)
    val prefixBefore = driver.typedPrefixLength(uri)
    val (touchedBefore, _, _) = scopeCounts()

    // The run whose typer polled the checker, and its tree count at the last poll:
    // for a fresh run that is aborted this is the only trace of it.
    @volatile var polledRun: Run | Null = null
    @volatile var polledCount = 0
    var polls = 0
    val start = System.nanoTime()
    val deadline = if cancelAfterMs >= 0 then start + cancelAfterMs * 1000000L else Long.MaxValue
    val checker: () => Boolean = () =>
      polls += 1
      val run = driver.currentCtx.run
      if run != null then
        polledRun = run
        polledCount = typedTreeCount(run)
      System.nanoTime() >= deadline

    val countBefore =
      val run = driver.currentCtx.run
      if run != null then typedTreeCount(run) else 0

    var cancelled = false
    var error: String | Null = null
    var completions: List[Completion] = Nil
    var diagnostics = 0
    try
      driver.withCancelChecker(checker) {
        kind match
          case "full" =>
            diagnostics = driver.run(uri, source).size
          case _ =>
            diagnostics = driver.runUpTo(uri, source, Span(offset)).size
            driver.compilationUnits.get(uri).foreach { unit =>
              given Context = driver.currentCtx.fresh.setCompilationUnit(unit).withPhase(Phases.typerPhase(using driver.currentCtx))
              val pos = SourcePosition(source, Span(offset))
              completions = Completion.completions(pos)._2
            }
      }
    catch
      case _: CompilationUnit.CancelledCompilation => cancelled = true
      case scala.util.control.NonFatal(ex) => error = ex.toString
    val ms = (System.nanoTime() - start) / 1000000.0

    val runIdAfter = driver.currentCtx.runId
    val sessionRunAfter = driver.runIdOf(uri)
    val prefixAfter = driver.typedPrefixLength(uri)
    val typedAfter = typedSpans(source)
    val (touched, completed, total) = scopeCounts()
    val runAfter = driver.currentCtx.run
    val countAfter = if runAfter != null then typedTreeCount(runAfter) else 0
    val sameRun = runIdAfter == runIdBefore
    val typedTrees =
      if cancelled && polledRun != null && polledRun.runContext.runId != runIdBefore then polledCount
      else if sameRun then countAfter - countBefore
      else countAfter

    val statRows = stats.map { st =>
      val before = isTyped(st, typedBefore)
      val after = isTyped(st, typedAfter)
      val state = if after && before then "typed" else if after then "typed-now" else "untyped"
      Map("name" -> st.name, "start" -> st.start, "end" -> st.end, "state" -> state)
    }
    val cursorStat = stats.indexWhere(st => st.start <= offset && offset <= st.end)
    val firstUntyped = stats.indexWhere(st => !isTyped(st, typedAfter))

    val outcome =
      if error != null then "error"
      else if cancelled then
        if sessionRunAfter == -1 then "cancelled-fresh"
        else "cancelled-resume"
      else if kind == "full" then "full"
      else if !sameRun then "fresh"
      else if prefixAfter > prefixBefore then "resumed"
      else "from-prefix"

    val where =
      if !cancelled then null
      else if sessionRunAfter == -1 then "a fresh run, discarded whole (the driver restored the previous context)"
      else if firstUntyped >= 0 then s"while typing ${stats(firstUntyped).name}: the prefix keeps the ${prefixAfter} trees typed before it"
      else "after the last statement"

    Map(
      "kind" -> kind, "offset" -> offset, "cancelAfterMs" -> cancelAfterMs,
      "outcome" -> outcome, "where" -> where, "error" -> error,
      "runIdBefore" -> runIdBefore, "runId" -> runIdAfter, "runChanged" -> !sameRun,
      "sessionRunBefore" -> sessionRunBefore, "sessionRun" -> sessionRunAfter,
      "prefixBefore" -> prefixBefore, "prefix" -> prefixAfter,
      "fullyTyped" -> driver.isFullyTyped(uri),
      "statements" -> statRows, "cursorStatement" -> cursorStat,
      "typedStatements" -> statRows.count(_("state") != "untyped"),
      "typedNow" -> statRows.count(_("state") == "typed-now"),
      "typedTrees" -> typedTrees, "polls" -> polls,
      "ms" -> math.round(ms * 10) / 10.0,
      "touched" -> touched, "touchedBefore" -> touchedBefore, "completed" -> completed, "scopeSize" -> total,
      "diagnostics" -> diagnostics,
      "completions" -> completions.map(c => c.label + (if c.description.nonEmpty then " " + c.description else "")).take(50)
    )
  }

  private def findPage(): Path =
    sys.props.get("xray.page").map(Paths.get(_)).filter(Files.exists(_)).getOrElse {
      val rel = Paths.get("presentation-compiler", "test", "dotty", "tools", "pc", "xray", "xray.html")
      Iterator.iterate(Paths.get("").toAbsolutePath)(_.getParent).takeWhile(_ != null).map(_.resolve(rel)).find(Files.exists(_))
        .getOrElse(throw new IllegalStateException(s"xray.html not found from ${Paths.get("").toAbsolutePath}; pass -Dxray.page"))
    }

  private def readBody(ex: HttpExchange): String =
    new String(ex.getRequestBody.readAllBytes(), StandardCharsets.UTF_8)

  /** The request body is `{"kind","code","offset","cancelAfterMs"}`; the
   *  code is sent URL-encoded as a separate field to keep the parser trivial.
   */
  private def field(body: String, name: String): Option[String] =
    body.split('&').map(_.split("=", 2)).collectFirst { case Array(k, v) if k == name => java.net.URLDecoder.decode(v, StandardCharsets.UTF_8) }

  private def reply(ex: HttpExchange, status: Int, contentType: String, body: String): Unit =
    val bytes = body.getBytes(StandardCharsets.UTF_8)
    ex.getResponseHeaders.add("Content-Type", contentType)
    ex.getResponseHeaders.add("Cache-Control", "no-store")
    ex.sendResponseHeaders(status, bytes.length)
    val out = ex.getResponseBody
    out.write(bytes); out.close()

  def main(args: Array[String]): Unit =
    val port = sys.props.get("xray.port").map(_.toInt).getOrElse(8791)
    val page = findPage()
    println(s"[xray] page: $page")
    println(s"[xray] warming up the driver on other content")
    val t0 = System.nanoTime()
    driver.run(uri, SourceFile.virtual(uri, generatedSource("warmup", 5)))
    println(f"[xray] warm-up full run: ${(System.nanoTime() - t0) / 1e6}%.0f ms")
    val server = HttpServer.create(new InetSocketAddress("127.0.0.1", port), 0)
    server.createContext("/", ex => ex.getRequestURI.getPath match
      case "/" | "/index.html" =>
        reply(ex, 200, "text/html; charset=utf-8", Files.readString(page))
      case "/source" =>
        reply(ex, 200, "application/json", json(Map("source" -> generatedSource("x-ray demo"), "objects" -> objectCount)))
      case "/request" if ex.getRequestMethod == "POST" =>
        val body = readBody(ex)
        val kind = field(body, "kind").getOrElse("complete")
        val code = field(body, "code").getOrElse("")
        val offset = field(body, "offset").map(_.toInt).getOrElse(0)
        val cancel = field(body, "cancelAfterMs").map(_.toLong).getOrElse(-1L)
        val result =
          try request(kind, code, offset, cancel)
          catch case scala.util.control.NonFatal(ex) => Map("outcome" -> "error", "error" -> ex.toString)
        println(s"[xray] $kind@$offset cancel=$cancel -> ${result("outcome")} run=${result.getOrElse("runId", "?")} prefix=${result.getOrElse("prefixBefore", "?")}->${result.getOrElse("prefix", "?")} ${result.getOrElse("ms", "?")}ms")
        reply(ex, 200, "application/json", json(result))
      case _ =>
        reply(ex, 404, "text/plain", "not found"))
    server.start()
    println(s"[xray] listening on http://127.0.0.1:$port/")
    Thread.currentThread.join()
