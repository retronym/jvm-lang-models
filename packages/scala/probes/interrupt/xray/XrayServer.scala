package dotty.tools.pc.xray

import java.io.File
import java.net.{InetSocketAddress, URI}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import scala.language.unsafeNulls
import scala.jdk.CollectionConverters.*

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

/** A toy IDE over the patched `InteractiveDriver` (targeted typing along the
 *  path to the target, resumable runs, cancellation that unwinds): one page, one virtual file `A.scala`,
 *  and an x-ray of what the driver did for each request. Every number in the
 *  x-ray is read from the driver; nothing is simulated.
 *
 *  Run from the scala3 worktree with the session patch applied:
 *    sbt --mem 8192 "scala3-presentation-compiler/Test/runMain dotty.tools.pc.xray.XrayServer"
 *  then open http://127.0.0.1:8791/ (`-Dxray.port` to change).
 */
object XrayServer:

  val generatedUri: URI = URI.create("file:///A.scala")
  val objectCount = 60

  /** A snapshot of the compiler's sources at the base commit, for the
   *  real-sources mode: `out/xray-sources`, made from the worktree root with
   *  `git archive d168df2a76 compiler/src/dotty/tools/dotc | tar -x -C out/xray-sources`
   *  (found by walking up from the working directory), or `-Dxray.sources=<dir>`.
   *  A snapshot rather than the live checkout, so that the files do not move
   *  under the page and the patch's own edits are not what is shown.
   */
  private val sourcesRoot: Option[Path] =
    sys.props.get("xray.sources").map(Paths.get(_)).filter(Files.isDirectory(_)).orElse(
      Iterator.iterate(Paths.get("").toAbsolutePath)(_.getParent).takeWhile(_ != null)
        .map(_.resolve("out/xray-sources/compiler/src/dotty/tools/dotc")).find(Files.isDirectory(_)))

  /** Paths of the snapshot's sources, relative to the root, package by package. */
  private def sourceFiles(): List[String] = sourcesRoot match
    case None => Nil
    case Some(root) =>
      val s = Files.walk(root)
      try s.iterator().asScala.filter(f => f.toString.endsWith(".scala")).map(f => root.relativize(f).toString).toList.sorted
      finally s.close()

  /** The uri of the file a request is on: the generated one, or a real source. */
  private def uriOf(file: String): URI =
    if file.isEmpty then generatedUri
    else sourcesRoot.map(_.resolve(file).toUri).getOrElse(generatedUri)

  /** The same shape as `CompletionSessionSuite.bigSource`, without the marker;
   *  the last object also has a `giant` method of 200 local vals, big enough
   *  for a cancellation to land inside it (the typer polls every 1024 trees),
   *  that starts with `tests.macros.Latch.await`, a macro that blocks the typer while
   *  the latch file exists (see `Latch` in the testcases project).
   */
  def generatedSource(tag: String, n: Int = objectCount): String =
    val objects = (0 until n).map { i =>
      val giant =
        if i == n - 1 then "\n  def giant(xs: List[Int]): Int = {\n    val latched = tests.macros.Latch.await // a macro: blocks the typer while the server's latch is armed\n" + (0 until 200).map(j => s"    val a$j = xs.map(_ + $j).filter(_ > $j).sum").mkString("\n") + "\n    a0 + a199\n  }"
        else ""
      s"""|object M$i {
          |  def method$i(xs: List[Int]): Int = xs.map(_ + $i).filter(_ > $i).sum$giant
          |  val r = this.meth
          |}""".stripMargin
    }.mkString("\n")
    s"// $tag\n$objects\n"

  /** The whole test JVM's classpath, so that the compiler's own sources
   *  resolve against its classes (the generated file sees it too).
   */
  private val settings =
    List("-color:never", "-Ximport-suggestion-timeout", "0",
      "-classpath", sys.props.getOrElse("java.class.path", BuildInfo.ideTestsDependencyClasspath.map(_.toPath.toString).mkString(File.pathSeparator)))

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
    // `package a.b.c` at the top wraps the whole file in a nested PackageDef: show its statements
    def statsOf(t: untpd.Tree): List[untpd.Tree] = t match
      case untpd.PackageDef(_, (inner: untpd.PackageDef) :: Nil) => statsOf(inner)
      case untpd.PackageDef(_, stats) => stats
      case _ => Nil
    val stats = statsOf(tree)
    stats.map { s =>
      val name = s match
        case m: untpd.ModuleDef => s"object ${m.name}"
        case t: untpd.TypeDef => s"${if t.mods.is(dotty.tools.dotc.core.Flags.Trait) then "trait" else "class"} ${t.name}"
        case d: untpd.DefDef => s"def ${d.name}"
        case v: untpd.ValDef => s"val ${v.name}"
        case i: untpd.Import => s"import ${i.expr.show.take(30)}"
        case p: untpd.PackageDef => s"package ${p.pid.show}"
        case other => other.getClass.getSimpleName
      Stat(name, s.span.start, s.span.end)
    }

  /** The spans of the typed statements of the current unit of `uri`, if that
   *  unit is for `source` (after an aborted fresh run the previous unit stays
   *  current, and must not be read as typed state of the new content).
   */
  private def typedSpans(uri: URI, source: SourceFile): List[Span] =
    def spansOf(t: tpd.Tree): List[Span] = t match
      case tpd.PackageDef(_, (inner: tpd.PackageDef) :: Nil) => spansOf(inner)
      case tpd.PackageDef(_, stats) => stats.map(_.span)
      case _ => Nil
    driver.compilationUnits.get(uri) match
      case Some(unit) if unit.source.textContent() == source.textContent() => spansOf(unit.tpdTree)
      case _ => Nil

  private def isTyped(stat: Stat, spans: List[Span]): Boolean =
    spans.exists(sp => sp.exists && sp.start <= stat.start && stat.end <= sp.end)

  /** Symbols of this file in the empty package's scope: how many have `Touched`
   *  set without being completed (`isCompleting`), and how many are completed.
   */
  private def scopeCounts(uri: URI): (Int, Int, Int) =
    given Context = driver.currentCtx
    val file = driver.openedFiles.get(uri).map(_.file)
    def ofFile(s: Symbol) = file.exists(f => s.associatedFile != null && s.associatedFile.path == f.path)
    // The packages the file's symbols live in: from the root, through the package clause
    def walk(pkg: Symbol): List[Symbol] =
      pkg.info.decls.toList.flatMap { s =>
        if s.is(dotty.tools.dotc.core.Flags.Package) then walk(s.moduleClass)
        else if ofFile(s) then List(s)
        else Nil
      }
    val syms = walk(defn.RootClass)
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

  /** The latch file `xray.Latch.await` polls, armed for a latched request. */
  private val latchFile: Option[java.io.File] = sys.props.get("xray.latch").map(new java.io.File(_))
  private def armLatch(): Unit = latchFile.foreach { f => f.getParentFile.mkdirs(); f.createNewFile() }
  private def releaseLatch(): Unit = latchFile.foreach(_.delete())
  private def latched: Boolean = latchFile.exists(_.exists())

  /** The request in flight (a latched one runs on its own thread), its
   *  result once done, and the cancel flag the checker polls.
   */
  @volatile private var inFlight: Map[String, Any] | Null = null
  @volatile private var lastResult: Map[String, Any] | Null = null
  @volatile private var cancelNow = false
  @volatile private var countAtStart = 0
  @volatile private var runAtStart: Run | Null = null
  @volatile private var startedAt = 0L

  /** Trees typed by the request in flight: the run's counter less what it
   *  was at the start, or the whole counter if the request started a run.
   */
  private def treesSoFar: Int =
    val run = driver.currentCtx.run
    if run == null then 0
    else if run eq runAtStart then typedTreeCount(run) - countAtStart
    else typedTreeCount(run)

  private def status(): Map[String, Any] =
    val f = inFlight
    Map("inFlight" -> (f != null), "request" -> f, "latched" -> latched, "cancelRequested" -> cancelNow,
      "treesSoFar" -> (if f != null then treesSoFar else 0),
      "elapsedMs" -> (if f != null then (System.nanoTime() - startedAt) / 1000000 else 0),
      "result" -> lastResult)

  /** One request against the driver, with its x-ray. `kind` is `complete`
   *  (`runUpTo` at `offset`, then the completions there) or `full` (`run`);
   *  `cancelAfterMs >= 0` installs a cancel checker that fires that long after
   *  the request started.
   */
  def request(kind: String, code: String, offset: Int, cancelAfterMs: Long, latch: Boolean = false, file: String = ""): Map[String, Any] = lock.synchronized {
    cancelNow = false
    if latch then armLatch() else releaseLatch()
    inFlight = Map("kind" -> kind, "offset" -> offset, "cancelAfterMs" -> cancelAfterMs, "latch" -> latch)
    startedAt = System.nanoTime()
    locally {
      val run = driver.currentCtx.run
      runAtStart = run
      countAtStart = if run == null then 0 else typedTreeCount(run)
    }
    try
      val r = request0(uriOf(file), kind, code, offset, cancelAfterMs) + ("latch" -> latch) + ("cancelledByButton" -> cancelNow) + ("file" -> file)
      lastResult = r
      r
    finally
      inFlight = null
      releaseLatch()
  }

  private def request0(uri: URI, kind: String, code: String, offset: Int, cancelAfterMs: Long): Map[String, Any] = {
    val source = SourceFile.virtual(uri, code)
    val stats = statements(source)
    val typedBefore = typedSpans(uri, source)
    val runIdBefore = driver.currentCtx.runId
    val sessionRunBefore = driver.runIdOf(uri)
    val prefixBefore = driver.typedPrefixLength(uri)
    val (touchedBefore, _, _) = scopeCounts(uri)

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
      cancelNow || System.nanoTime() >= deadline

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
    val typedAfter = typedSpans(uri, source)
    val untypedAfter = driver.untypedSpans(uri)
    val (touched, completed, total) = scopeCounts(uri)
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
      // Members of this statement the targeted run skipped (typed statements only)
      val skippedMembers = untypedAfter.filter(sp => st.start <= sp.start && sp.end <= st.end && !(sp.start == st.start && sp.end == st.end))
      Map("name" -> st.name, "start" -> st.start, "end" -> st.end, "state" -> state,
        "skippedMembers" -> skippedMembers.map(sp => Map("start" -> sp.start, "end" -> sp.end, "text" -> code.substring(sp.start, math.min(sp.end, sp.start + 40)).takeWhile(_ != '\n'))))
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
      else if cursorStat >= 0 then s"while typing ${stats(cursorStat).name}: it is re-parsed and re-indexed, everything typed before stays"
      else "outside any statement"

    Map(
      "kind" -> kind, "offset" -> offset, "cancelAfterMs" -> cancelAfterMs,
      "outcome" -> outcome, "where" -> where, "error" -> error,
      "runIdBefore" -> runIdBefore, "runId" -> runIdAfter, "runChanged" -> !sameRun,
      "sessionRunBefore" -> sessionRunBefore, "sessionRun" -> sessionRunAfter,
      "prefixBefore" -> prefixBefore, "prefix" -> prefixAfter,
      "fullyTyped" -> driver.isFullyTyped(uri),
      "tainted" -> driver.isTainted(uri),
      "cyclesPrevented" -> (if runAfter != null then runAfter.cyclesPrevented.size else 0),
      "statements" -> statRows, "cursorStatement" -> cursorStat,
      "typedStatements" -> statRows.count(_("state") != "untyped"),
      "typedNow" -> statRows.count(_("state") == "typed-now"),
      "typedTrees" -> typedTrees, "polls" -> polls,
      "untypedSpans" -> untypedAfter.size,
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
    println(s"[xray] latch file: ${latchFile.map(_.getPath).getOrElse("none (-Dxray.latch not set: latched requests disabled)")}")
    releaseLatch()
    println(s"[xray] warming up the driver on other content")
    val t0 = System.nanoTime()
    driver.run(generatedUri, SourceFile.virtual(generatedUri, generatedSource("warmup", 5)))
    println(s"[xray] compiler sources: ${sourcesRoot.map(r => s"$r (${sourceFiles().size} files)").getOrElse("not found")}")
    println(f"[xray] warm-up full run: ${(System.nanoTime() - t0) / 1e6}%.0f ms")
    val server = HttpServer.create(new InetSocketAddress("127.0.0.1", port), 0)
    server.createContext("/", ex => ex.getRequestURI.getPath match
      case "/" | "/index.html" =>
        reply(ex, 200, "text/html; charset=utf-8", Files.readString(page))
      case "/source" =>
        val query = Option(ex.getRequestURI.getRawQuery).getOrElse("")
        val file = field(query, "file").getOrElse("")
        val source =
          if file.isEmpty then generatedSource("x-ray demo")
          else sourcesRoot.map(root => Files.readString(root.resolve(file))).getOrElse("// no compiler sources found")
        reply(ex, 200, "application/json", json(Map("source" -> source, "file" -> file, "objects" -> objectCount)))
      case "/files" =>
        reply(ex, 200, "application/json", json(Map("root" -> sourcesRoot.map(_.toString).getOrElse(""), "files" -> sourceFiles())))
      case "/request" if ex.getRequestMethod == "POST" =>
        val body = readBody(ex)
        val kind = field(body, "kind").getOrElse("complete")
        val code = field(body, "code").getOrElse("")
        val offset = field(body, "offset").map(_.toInt).getOrElse(0)
        val cancel = field(body, "cancelAfterMs").map(_.toLong).getOrElse(-1L)
        val latch = field(body, "latch").contains("1")
        val file = field(body, "file").getOrElse("")
        def go(): Map[String, Any] =
          val result =
            try request(kind, code, offset, cancel, latch, file)
            catch case scala.util.control.NonFatal(ex) => Map("outcome" -> "error", "error" -> ex.toString)
          println(s"[xray] $kind@$offset cancel=$cancel latch=$latch -> ${result("outcome")} run=${result.getOrElse("runId", "?")} typed=${result.getOrElse("prefixBefore", "?")}->${result.getOrElse("prefix", "?")} ${result.getOrElse("ms", "?")}ms")
          result
        if latch then
          // Runs on its own thread; the page polls /status and releases or cancels.
          if latchFile.isEmpty then reply(ex, 400, "text/plain", "the server was started without -Dxray.latch")
          else
            val t = new Thread((() => { lastResult = null; go(); () }): Runnable, "xray-latched-request")
            t.setDaemon(true); t.start()
            while inFlight == null && t.isAlive do Thread.sleep(5)
            reply(ex, 202, "application/json", json(status()))
        else reply(ex, 200, "application/json", json(go()))
      case "/status" =>
        reply(ex, 200, "application/json", json(status()))
      case "/release" if ex.getRequestMethod == "POST" =>
        releaseLatch()
        reply(ex, 200, "application/json", json(status()))
      case "/cancel" if ex.getRequestMethod == "POST" =>
        // The checker sees the flag at the next checkpoint (every 1024 typed trees); the latch is released so that typing gets there.
        cancelNow = true
        releaseLatch()
        reply(ex, 200, "application/json", json(status()))
      case _ =>
        reply(ex, 404, "text/plain", "not found"))
    server.start()
    println(s"[xray] listening on http://127.0.0.1:$port/")
    Thread.currentThread.join()
