package compileserver;

import dotty.tools.dotc.Compiler;
import dotty.tools.dotc.Driver;
import dotty.tools.dotc.core.Contexts;
import dotty.tools.dotc.interfaces.Diagnostic;
import dotty.tools.dotc.interfaces.SourcePosition;
import dotty.tools.dotc.reporting.Reporter;
import dotty.tools.io.AbstractFile;
import dotty.tools.io.Directory;
import dotty.tools.io.PlainDirectory;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.function.Consumer;
import java.util.regex.Pattern;
import scala.jdk.javaapi.CollectionConverters;

/**
 * dotc (Scala 3), in one of two modes ({@code --base}):
 *
 * <ul>
 *   <li>{@code cached} (the default): one root context per option list, set up by the driver over a
 *       {@code ContextBase} that is kept, and a fresh {@code Compiler}, run and context per program, as the REPL
 *       and the sbt bridge do. A request with a classpath gets a throwaway base.
 *   <li>{@code fresh}: the command-line entry point, {@code Driver.process(args, SimpleReporter, callback)}, with
 *       the {@code dotty.tools.dotc.interfaces} diagnostics that sbt and the IDEs use: the lowest coupling to the
 *       compiler, a fresh {@code ContextBase} per program, about six times slower (compile-server.md, Timings).
 * </ul>
 *
 * Sources given as text are written next to the output directory, since both take files.
 *
 * <p>Arguments: {@code --library CP} (the classpath every program compiles and runs against) and
 * {@code --base cached|fresh}.
 */
public final class DotcBackend implements Backend {
  private final List<String> library = new ArrayList<>();
  private boolean cachedMode = true;
  /** The driver's closing count ("1 error found"), which it reports as a diagnostic without a position. */
  private static final Pattern SUMMARY = Pattern.compile("\\d+ (errors?|warnings?)( and \\d+ (errors?|warnings?))? found");

  private Contexts.Context root;
  private List<String> rootOptions;

  public DotcBackend(String[] args) {
    for (int i = 0; i < args.length; i++) {
      if (args[i].equals("--library") && i + 1 < args.length) {
        for (String p : args[++i].split(File.pathSeparator)) if (!p.isEmpty()) library.add(p);
      } else if (args[i].equals("--base") && i + 1 < args.length) {
        cachedMode = args[++i].equals("cached");
      } else throw new IllegalArgumentException("usage: DotcBackend --library CP [--base cached|fresh]");
    }
  }

  /** The driver's setup over a new ContextBase, with no sources required. */
  private static final class Setup extends Driver {
    @Override public boolean sourcesRequired() { return false; }
    Contexts.Context root(List<String> args) {
      Contexts.Context initial = new Contexts.ContextBase().initialCtx();
      return setup(args.toArray(new String[0]), initial).get()._2();
    }
  }

  @Override
  public boolean compile(List<Source> sources, List<String> options, List<Path> classpath, Path out,
                         List<Map<String, Object>> diagnostics) throws Exception {
    List<String> cp = new ArrayList<>(library);
    for (Path p : classpath) cp.add(p.toString());
    List<String> settings = new ArrayList<>(options);
    settings.addAll(Arrays.asList("-classpath", String.join(File.pathSeparator, cp)));
    Map<String, String> names = new HashMap<>();  // the path dotc sees to the name the request gave
    List<String> files = new ArrayList<>();
    Path srcDir = out.resolveSibling(out.getFileName() + ".src");
    for (Source s : sources) {
      Path p = Paths.get(s.name);
      if (!p.isAbsolute() || !Files.exists(p)) {
        p = srcDir.resolve(s.name);
        Files.createDirectories(p.getParent());
        Files.write(p, s.content.getBytes(StandardCharsets.UTF_8));
      }
      names.put(p.toString(), s.name);
      files.add(p.toString());
    }
    Consumer<Diagnostic> report = d -> {
      if (!d.position().isPresent() && SUMMARY.matcher(d.message()).matches()) return;
      Map<String, Object> m = new LinkedHashMap<>();
      Optional<SourcePosition> pos = d.position();
      String path = pos.map(x -> x.source().path()).orElse(null);
      m.put("file", path == null ? null : names.getOrDefault(path, path));
      m.put("line", pos.map(x -> x.line() + 1).orElse(0));
      m.put("column", pos.map(x -> x.column() + 1).orElse(0));
      m.put("severity", d.level() == Diagnostic.ERROR ? "ERROR" : d.level() == Diagnostic.WARNING ? "WARNING" : "INFO");
      m.put("message", d.message());
      diagnostics.add(m);
    };
    if (!cachedMode) {
      List<String> args = new ArrayList<>(settings);
      args.addAll(Arrays.asList("-d", out.toString()));
      args.addAll(files);
      new Driver().process(args.toArray(new String[0]), report::accept, null);
      return true;
    }
    boolean fresh = false;
    Contexts.Context base;
    if (!classpath.isEmpty()) base = new Setup().root(settings);
    else {
      if (root == null || !options.equals(rootOptions)) {
        root = new Setup().root(settings);
        rootOptions = options;
        fresh = true;
      }
      base = root;
    }
    // the reporter Driver.process makes of a SimpleReporter: one message per position, as on the console
    Contexts.FreshContext ctx = base.fresh().setReporter(Reporter.fromSimpleReporter(report::accept));
    ctx.setSetting(ctx.settings().outputDir(), new PlainDirectory(new Directory(out)));
    List<AbstractFile> afs = new ArrayList<>();
    for (String f : files) afs.add(AbstractFile.getFile(f));
    new Setup().doCompile(new Compiler(), CollectionConverters.asScala(afs).toList(), ctx);
    return fresh;
  }

  @Override
  public void recycle() {
    root = null;
    rootOptions = null;
  }

  @Override
  public List<Path> library() {
    List<Path> r = new ArrayList<>();
    for (String p : library) r.add(Paths.get(p));
    return r;
  }
}
