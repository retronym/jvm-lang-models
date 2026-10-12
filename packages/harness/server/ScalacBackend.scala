package compileserver

import java.io.File
import java.nio.file.{Path, Paths}
import java.util.{LinkedHashMap, List => JList, Map => JMap}

import scala.reflect.internal.util.BatchSourceFile
import scala.reflect.io.VirtualFile
import scala.tools.nsc.{Global, Settings}
import scala.tools.nsc.reporters.StoreReporter

/** scalac 2 (2.12, 2.13): one cached `Global` per option list, a `new Run` per program, as Zinc's
  * `CachedCompiler` does. A request with a classpath compiles in a throwaway `Global`.
  *
  * Arguments: `--library CP`, the classpath every program compiles and runs against (scala-library).
  */
final class ScalacBackend(args: Array[String]) extends Backend {
  private val libraryCp: List[String] = args.toList match {
    case List("--library", cp) => cp.split(File.pathSeparator).toList.filter(_.nonEmpty)
    case _ => throw new IllegalArgumentException("usage: ScalacBackend --library CP")
  }

  private var cached: Global = null
  private var cachedOptions: JList[String] = null

  private def newGlobal(options: JList[String], classpath: JList[Path]): Global = {
    val settings = new Settings(msg => throw new IllegalArgumentException(msg))
    val opts = (0 until options.size).map(options.get).toList
    val (ok, rest) = settings.processArguments(opts, processAll = true)
    if (!ok || rest.nonEmpty) throw new IllegalArgumentException("bad options: " + opts.mkString(" "))
    val extra = (0 until classpath.size).map(i => classpath.get(i).toString).toList
    settings.classpath.value = (libraryCp ++ extra).mkString(File.pathSeparator)
    new Global(settings, new StoreReporter(settings))
  }

  override def compile(sources: JList[Backend.Source], options: JList[String], classpath: JList[Path], out: Path,
                       diagnostics: JList[JMap[String, AnyRef]]): Boolean = {
    var fresh = false
    val global =
      if (!classpath.isEmpty) newGlobal(options, classpath)
      else {
        if (cached == null || cachedOptions != options) {
          cached = newGlobal(options, classpath)
          cachedOptions = options
          fresh = true
        }
        cached
      }
    val reporter = global.reporter.asInstanceOf[StoreReporter]
    reporter.reset()
    global.settings.outputDirs.setSingleOutput(out.toString)
    val files = (0 until sources.size).map { i =>
      val s = sources.get(i)
      // named by its base name, as scalac names a file on disk, so the SourceFile attribute is the same
      new BatchSourceFile(new VirtualFile(Paths.get(s.name).getFileName.toString, s.name), s.content.toCharArray)
    }.toList
    try new global.Run().compileSources(files)
    finally if (global ne cached) global.close()
    for (info <- reporter.infos) {
      val m = new LinkedHashMap[String, AnyRef]
      val pos = info.pos
      m.put("file", if (pos.isDefined) pos.source.path else null)
      m.put("line", Integer.valueOf(if (pos.isDefined) pos.line else 0))
      m.put("column", Integer.valueOf(if (pos.isDefined) pos.column else 0))
      m.put("severity", info.severity.toString)
      m.put("message", info.msg)
      diagnostics.add(m)
    }
    reporter.reset()
    fresh
  }

  override def recycle(): Unit = {
    if (cached != null) cached.close()
    cached = null
    cachedOptions = null
  }

  override def library(): JList[Path] = {
    val l = new java.util.ArrayList[Path]
    libraryCp.foreach(p => l.add(Paths.get(p)))
    l
  }
}
