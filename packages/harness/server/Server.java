package compileserver;

import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.security.MessageDigest;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * A long-lived compiler: JSON-lines requests on stdin, one JSON-line response per request on stdout. See
 * packages/harness/docs/compile-server.md.
 *
 * <pre>
 *   Server --backend CLASS --work DIR [--recycle N] [-- BACKEND-ARGS...]
 * </pre>
 *
 * Request: {@code id}, {@code op} (compile, run, recycle), and for compile: {@code sources} (file name to text)
 * and/or {@code files} (paths read by the server), {@code options}, {@code classpath} (ids of earlier compiles or
 * directories), {@code out} (default WORK/id). For run: {@code classpath}, {@code main} (default Main),
 * {@code args}, {@code timeout} (ms, default 10000).
 *
 * <p>Response: {@code id}, {@code ok}, {@code ms}; for compile {@code diagnostics}, {@code out}, {@code classes}
 * (class name to digest), {@code fresh}; for run {@code stdout}, {@code stderr}, {@code exception};
 * {@code crash} when the server itself threw. A run that times out answers {@code timeout: true} and the server
 * exits, since its thread cannot be stopped; the client restarts it.
 */
public final class Server {
  /** System.out and System.err for everyone but the protocol, switched to a buffer during a run. */
  static final class Switch extends OutputStream {
    private final OutputStream fallback;
    volatile ByteArrayOutputStream target;
    Switch(OutputStream fallback) { this.fallback = fallback; }
    @Override public void write(int b) throws IOException { OutputStream t = target; (t != null ? t : fallback).write(b); }
    @Override public void write(byte[] b, int off, int len) throws IOException {
      OutputStream t = target; (t != null ? t : fallback).write(b, off, len);
    }
    @Override public void flush() throws IOException { fallback.flush(); }
  }

  private final Backend backend;
  private final Path work;
  private final int recycleEvery;
  private final PrintStream protocol;
  private final Switch out, err;
  private final Map<String, Path> outputs = new HashMap<>();
  /** Top-level packages (or top-level names, outside a package) compiled by the cached instance. */
  private final Set<String> seen = new HashSet<>();
  private int sinceFresh;
  private ClassLoader libraryLoader;

  private Server(Backend backend, Path work, int recycleEvery, PrintStream protocol, Switch out, Switch err) {
    this.backend = backend; this.work = work; this.recycleEvery = recycleEvery;
    this.protocol = protocol; this.out = out; this.err = err;
  }

  public static void main(String[] args) throws Exception {
    String backendClass = null;
    Path work = null;
    int recycle = 1000;
    List<String> rest = new ArrayList<>();
    for (int i = 0; i < args.length; i++) {
      switch (args[i]) {
        case "--backend": backendClass = args[++i]; break;
        case "--work": work = Paths.get(args[++i]); break;
        case "--recycle": recycle = Integer.parseInt(args[++i]); break;
        case "--": rest.addAll(Arrays.asList(args).subList(i + 1, args.length)); i = args.length; break;
        default: throw new IllegalArgumentException("unknown argument " + args[i]);
      }
    }
    if (backendClass == null || work == null) throw new IllegalArgumentException("usage: Server --backend CLASS --work DIR");
    Files.createDirectories(work);
    PrintStream protocol = new PrintStream(new FileOutputStream(FileDescriptor.out), false, "UTF-8");
    Switch out = new Switch(new FileOutputStream(FileDescriptor.err));
    Switch err = new Switch(new FileOutputStream(FileDescriptor.err));
    System.setOut(new PrintStream(out, true, "UTF-8"));
    System.setErr(new PrintStream(err, true, "UTF-8"));
    Backend backend = (Backend) Class.forName(backendClass).getConstructor(String[].class)
        .newInstance((Object) rest.toArray(new String[0]));
    new Server(backend, work, recycle, protocol, out, err).loop();
  }

  private void loop() throws IOException {
    BufferedReader in = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
    String line;
    while ((line = in.readLine()) != null) {
      if (line.trim().isEmpty()) continue;
      Map<String, Object> req = Json.obj(Json.parse(line));
      Map<String, Object> resp = new LinkedHashMap<>();
      resp.put("id", req.get("id"));
      long t0 = System.nanoTime();
      boolean exit = false;
      try {
        String op = (String) req.getOrDefault("op", "compile");
        switch (op) {
          case "compile": compile(req, resp); break;
          case "run": exit = run(req, resp); break;
          case "recycle": backend.recycle(); seen.clear(); sinceFresh = 0; resp.put("ok", true); break;
          default: throw new IllegalArgumentException("unknown op " + op);
        }
      } catch (Throwable t) {
        backend.recycle();
        seen.clear();
        sinceFresh = 0;
        StringWriter sw = new StringWriter();
        t.printStackTrace(new PrintWriter(sw));
        resp.put("ok", false);
        resp.put("crash", sw.toString());
      }
      resp.put("ms", (System.nanoTime() - t0) / 1_000_000);
      protocol.println(Json.write(resp));
      protocol.flush();
      if (exit) { protocol.close(); Runtime.getRuntime().halt(3); }
    }
  }

  private static final Pattern PACKAGE = Pattern.compile("^\\s*package\\s+([\\w.]+)\\s*;?\\s*$", Pattern.MULTILINE);
  private static final Pattern TOP = Pattern.compile(
      "^(?:(?:abstract|final|sealed|case|public|private|protected|implicit|open|transparent)\\s+)*" +
      "(?:class|trait|object|enum|interface|record|type|def|val)\\s+(\\w+)", Pattern.MULTILINE);

  /** What a source puts at top level: its first package clause, or the names it defines outside a package. */
  static Set<String> topLevel(Backend.Source s) {
    Set<String> r = new HashSet<>();
    Matcher p = PACKAGE.matcher(s.content);
    if (p.find()) { r.add(p.group(1)); return r; }
    Matcher m = TOP.matcher(s.content);
    while (m.find()) r.add("<empty>." + m.group(1));
    return r;
  }

  private void compile(Map<String, Object> req, Map<String, Object> resp) throws Exception {
    String id = String.valueOf(req.get("id"));
    List<Backend.Source> sources = new ArrayList<>();
    if (req.get("sources") != null)
      for (Map.Entry<String, Object> e : Json.obj(req.get("sources")).entrySet())
        sources.add(new Backend.Source(e.getKey(), (String) e.getValue()));
    for (String f : Json.strings(req.get("files")))
      sources.add(new Backend.Source(f, new String(Files.readAllBytes(Paths.get(f)), StandardCharsets.UTF_8)));
    List<Path> cp = classpath(req);
    Path dest = req.get("out") != null ? Paths.get((String) req.get("out")) : work.resolve(id);
    clean(dest);
    Files.createDirectories(dest);
    Set<String> tops = new HashSet<>();
    for (Backend.Source s : sources) tops.addAll(topLevel(s));
    if (cp.isEmpty() && (sinceFresh >= recycleEvery || !Collections.disjoint(tops, seen))) {
      backend.recycle();
      seen.clear();
      sinceFresh = 0;
    }
    List<Map<String, Object>> diags = new ArrayList<>();
    boolean fresh = backend.compile(sources, Json.strings(req.get("options")), cp, dest, diags);
    if (cp.isEmpty()) {
      if (fresh) { seen.clear(); sinceFresh = 0; }
      seen.addAll(tops);
      sinceFresh++;
    }
    outputs.put(id, dest);
    boolean ok = diags.stream().noneMatch(d -> "ERROR".equals(d.get("severity")));
    resp.put("ok", ok);
    resp.put("fresh", fresh);
    resp.put("diagnostics", diags);
    resp.put("out", dest.toString());
    resp.put("classes", digests(dest));
  }

  private List<Path> classpath(Map<String, Object> req) {
    List<Path> cp = new ArrayList<>();
    for (String e : Json.strings(req.get("classpath"))) cp.add(outputs.containsKey(e) ? outputs.get(e) : Paths.get(e));
    return cp;
  }

  private static void clean(Path dir) throws IOException {
    if (!Files.exists(dir)) return;
    try (Stream<Path> s = Files.walk(dir)) {
      for (Path p : (Iterable<Path>) s.sorted(Comparator.reverseOrder())::iterator) if (!p.equals(dir)) Files.delete(p);
    }
  }

  private static Map<String, Object> digests(Path dir) throws Exception {
    Map<String, Object> r = new TreeMap<>();
    MessageDigest md = MessageDigest.getInstance("SHA-256");
    try (Stream<Path> s = Files.walk(dir)) {
      for (Path p : (Iterable<Path>) s.filter(x -> x.toString().endsWith(".class")).sorted()::iterator) {
        String rel = dir.relativize(p).toString().replace(File.separatorChar, '/');
        byte[] h = md.digest(Files.readAllBytes(p));
        StringBuilder b = new StringBuilder();
        for (int k = 0; k < 8; k++) b.append(String.format("%02x", h[k]));
        r.put(rel.substring(0, rel.length() - ".class".length()), b.toString());
      }
    }
    return r;
  }

  /** Returns true when the run timed out and the server must exit. */
  private boolean run(Map<String, Object> req, Map<String, Object> resp) throws Exception {
    if (libraryLoader == null) {
      List<URL> urls = new ArrayList<>();
      for (Path p : backend.library()) urls.add(p.toUri().toURL());
      libraryLoader = new URLClassLoader(urls.toArray(new URL[0]), ClassLoader.getPlatformClassLoader());
    }
    List<URL> urls = new ArrayList<>();
    for (Path p : classpath(req)) urls.add(p.toUri().toURL());
    String main = (String) req.getOrDefault("main", "Main");
    String[] args = Json.strings(req.get("args")).toArray(new String[0]);
    long timeout = req.get("timeout") != null ? ((Number) req.get("timeout")).longValue() : 10_000;
    ByteArrayOutputStream bout = new ByteArrayOutputStream(), berr = new ByteArrayOutputStream();
    Throwable[] thrown = new Throwable[1];
    URLClassLoader loader = new URLClassLoader(urls.toArray(new URL[0]), libraryLoader);
    Thread th = new Thread(() -> {
      try {
        Method m = Class.forName(main, true, loader).getMethod("main", String[].class);
        m.invoke(null, (Object) args);
      } catch (InvocationTargetException e) {
        thrown[0] = e.getCause();
      } catch (Throwable t) {
        thrown[0] = t;
      }
    }, "run-" + req.get("id"));
    th.setContextClassLoader(loader);
    th.setDaemon(true);
    System.out.flush(); System.err.flush();
    out.target = bout; err.target = berr;
    try {
      th.start();
      th.join(timeout);
    } finally {
      System.out.flush(); System.err.flush();
      out.target = null; err.target = null;
    }
    boolean timedOut = th.isAlive();
    if (!timedOut) loader.close();
    resp.put("ok", !timedOut && thrown[0] == null);
    resp.put("stdout", bout.toString("UTF-8"));
    resp.put("stderr", berr.toString("UTF-8"));
    if (thrown[0] != null) resp.put("exception", thrown[0].toString());
    if (timedOut) resp.put("timeout", true);
    return timedOut;
  }
}
