package compileserver;

import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.*;
import javax.tools.*;

/** javac through javax.tools, in process. The file manager (and its caches of the platform classes) is kept. */
public final class JavacBackend implements Backend {
  private final JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
  private StandardJavaFileManager fm;
  private List<String> key;

  public JavacBackend(String[] args) {
    if (args.length != 0) throw new IllegalArgumentException("JavacBackend takes no arguments");
  }

  private static final class Src extends SimpleJavaFileObject {
    final String name, content;
    Src(String name, String content) {
      super(URI.create("string:///" + name.replace('\\', '/').replaceFirst("^/+", "")), Kind.SOURCE);
      this.name = name; this.content = content;
    }
    @Override public CharSequence getCharContent(boolean ignoreEncodingErrors) { return content; }
  }

  @Override
  public boolean compile(List<Source> sources, List<String> options, List<Path> classpath, Path out,
                         List<Map<String, Object>> diagnostics) throws Exception {
    boolean fresh = false;
    if (fm == null || !options.equals(key)) {
      recycle();
      fm = javac.getStandardFileManager(null, Locale.ROOT, StandardCharsets.UTF_8);
      key = options;
      fresh = true;
    }
    fm.setLocationFromPaths(StandardLocation.CLASS_OUTPUT, Collections.singletonList(out));
    fm.setLocationFromPaths(StandardLocation.CLASS_PATH, classpath);
    List<Src> units = new ArrayList<>();
    for (Source s : sources) units.add(new Src(s.name, s.content));
    DiagnosticCollector<JavaFileObject> dc = new DiagnosticCollector<>();
    javac.getTask(null, fm, dc, options, null, units).call();
    for (Diagnostic<? extends JavaFileObject> d : dc.getDiagnostics()) {
      Map<String, Object> m = new LinkedHashMap<>();
      JavaFileObject f = d.getSource();
      m.put("file", f instanceof Src ? ((Src) f).name : f == null ? null : f.getName());
      m.put("line", d.getLineNumber());
      m.put("column", d.getColumnNumber());
      m.put("severity", d.getKind() == Diagnostic.Kind.ERROR ? "ERROR"
          : d.getKind() == Diagnostic.Kind.NOTE || d.getKind() == Diagnostic.Kind.OTHER ? "INFO" : "WARNING");
      m.put("message", d.getMessage(Locale.ROOT));
      diagnostics.add(m);
    }
    return fresh;
  }

  @Override
  public void recycle() {
    if (fm != null) {
      try { fm.close(); } catch (Exception ignored) { }
    }
    fm = null;
    key = null;
  }

  @Override
  public List<Path> library() { return Collections.emptyList(); }
}
