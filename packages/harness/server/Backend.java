package compileserver;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;

/**
 * A compiler kept warm by {@link Server}. One request at a time. An implementation caches an instance keyed by its
 * options and compiles a request with a non-empty classpath in a throwaway instance.
 */
public interface Backend {
  final class Source {
    public final String name, content;
    public Source(String name, String content) { this.name = name; this.content = content; }
  }

  /**
   * Compiles {@code sources} into {@code out}, appending one map per diagnostic (file, line, column, severity,
   * message). Returns true when the cached instance was created for this request.
   */
  boolean compile(List<Source> sources, List<String> options, List<Path> classpath, Path out,
                  List<Map<String, Object>> diagnostics) throws Exception;

  /** Drops the cached instance; the next compile creates a fresh one. */
  void recycle();

  /** The library a compiled program runs against (scala-library), for the run op. */
  List<Path> library();
}
