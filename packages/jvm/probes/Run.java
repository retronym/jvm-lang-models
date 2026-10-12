import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.*;
import java.util.*;

/**
 * Runs each rendered case's client against `v0` and `v1` and compares the outcome with the model's.
 * Plain Java 17, so it runs on JDK 21 as well as on the JDK that rendered the classfiles.
 *
 * A client loads its classes (`Loads.run`, by `ldc`), then runs each site (`Site<k>.run`), each
 * verified just before it runs. The methods entered, and the classes whose fields a site read or
 * wrote, are read from `ProbeLog`; the outcome is their sequence over all sites (Track J4), or the
 * `Throwable`.
 *
 * Usage: java -cp classes Run cases.jsonl out
 * Prints one TSV row per case and world: case, world, model, JVM, verdict, JVM message; then a
 * summary line `#json {...}` (JDK, cases, disagreements, known deviations by bug) for the ledger
 * that `probe.sh` keeps with `RUNS=` (`runs/README.md`).
 */
public class Run {
  /** The model's `LinkError` constructors, with the JVM class each maps to. */
  static final Map<String, String> ERRORS = Map.of(
      "noClassDef", "java.lang.NoClassDefFoundError",
      "incompatibleClassChange", "java.lang.IncompatibleClassChangeError",
      "noSuchMethod", "java.lang.NoSuchMethodError",
      "abstractMethod", "java.lang.AbstractMethodError",
      "instantiation", "java.lang.InstantiationError",
      // HotSpot's class file parser, on JDK 21, 25 and 27; not the VerifyError older JDKs threw.
      "finalSuper", "java.lang.IncompatibleClassChangeError",
      "finalOverride", "java.lang.IncompatibleClassChangeError",
      "verify", "java.lang.VerifyError",
      "illegalAccess", "java.lang.IllegalAccessError",
      "noSuchField", "java.lang.NoSuchFieldError");

  public static void main(String[] args) throws Exception {
    Path out = Path.of(args[1]);
    int disagree = 0, cases = 0;
    Map<String, Integer> knownCount = new TreeMap<>();
    for (String line : Files.readAllLines(Path.of(args[0]))) {
      if (line.isBlank()) continue;
      Map<String, Object> k = Json.obj(Json.parse(line));
      String name = (String) k.get("name");
      cases++;
      for (String w : List.of("v0", "v1")) {
        String model = expected(Json.obj(k.get(w.equals("v0") ? "before" : "after")));
        String[] jvm = run(out.resolve(name), w, k);
        String verdict = model.equals(jvm[0]) ? "agree"
            : known(model, jvm) ? "known JDK-8356942"
            : knownSpecial(model, jvm, k) ? "known JDK-8350029" : "DISAGREE";
        if (verdict.equals("DISAGREE")) disagree++;
        else if (verdict.startsWith("known ")) knownCount.merge(verdict.substring(6), 1, Integer::sum);
        System.out.println(name + "\t" + w + "\t" + model + "\t" + jvm[0] + "\t" + verdict + "\t" + jvm[1]);
      }
    }
    System.out.println("# " + System.getProperty("java.vm.version") + ": " + disagree + " disagreements");
    StringBuilder known = new StringBuilder();
    knownCount.forEach((b, n) -> known.append(known.length() == 0 ? "" : ",").append('"').append(b).append("\":").append(n));
    System.out.println("#json {\"jdk\":\"" + System.getProperty("java.vm.version") + "\",\"cases\":" + cases
        + ",\"disagreements\":" + disagree + ",\"known\":{" + known + "}}");
    if (disagree > 0) System.exit(1);
  }

  /**
   * JDK-8356942 (fixed in 25): since JDK 10, `invokeinterface` on a receiver with conflicting
   * default methods throws AbstractMethodError, where JVMS §6.5 and `invokevirtual` say
   * IncompatibleClassChangeError.
   */
  static boolean known(String model, String[] jvm) {
    return Runtime.version().feature() < 25 && model.equals("java.lang.IncompatibleClassChangeError")
        && jvm[0].equals("java.lang.AbstractMethodError");
  }

  /**
   * JDK-8350029 (fixed in 25): before 25 the verifier checked a non-`<init>` `invokespecial` by the
   * constant's tag (an `InterfaceMethodref` must name a direct superinterface; a `Methodref` only
   * needs subtyping), so forms javac never emits fail in verification where 25+ fails in resolution,
   * and the reverse.
   */
  static boolean knownSpecial(String model, String[] jvm, Map<String, Object> k) {
    Set<String> both = Set.of(model, jvm[0]);
    if (Runtime.version().feature() >= 25 || !both.equals(Set.of("java.lang.VerifyError", "java.lang.IncompatibleClassChangeError"))) return false;
    for (Map<String, Object> s : Json.objs(k.get("sites"))) {
      if (s.get("op").equals("at") && Json.obj(s.get("site")).get("op").equals("invokespecial")) return true;
    }
    return false;
  }

  static String expected(Map<String, Object> o) {
    // `outOfFuel`, the model's bound on nested entries, maps to itself: no JVM outcome matches it.
    if (o.containsKey("error")) return ERRORS.getOrDefault((String) o.get("error"), (String) o.get("error"));
    return "ok " + Json.arr(o.get("ok"));
  }

  static String[] run(Path dir, String world, Map<String, Object> k) throws Exception {
    URL[] cp = { url(dir.resolve("client")), url(dir.resolve("sites")), url(dir.resolve(world)) };
    try (URLClassLoader l = new URLClassLoader(cp, Run.class.getClassLoader())) {
      List<String> ran = new ArrayList<>();
      try {
        call(l, "Loads");
        List<Map<String, Object>> sites = Json.objs(k.get("sites"));
        for (int i = 0; i < sites.size(); i++) {
          ProbeLog.reset();
          call(l, "Site" + i);
          for (Object e : ProbeLog.entered) ran.add(e instanceof ProbeLog.Put p ? written(p, l, k) : (String) e);
        }
        return new String[] { "ok " + ran, "" };
      } catch (Throwable t) {
        return new String[] { t.getClass().getName(), String.valueOf(t.getMessage()).lines().findFirst().orElse("") };
      }
    }
  }

  /** The class whose field a put wrote: the receiver's class or a superclass, or a loaded class's static field. */
  static String written(ProbeLog.Put p, ClassLoader l, Map<String, Object> k) throws Exception {
    if (p.obj() != null) {
      for (Class<?> c = p.obj().getClass(); c != null; c = c.getSuperclass()) {
        if (written(c, p.field(), p.obj())) return c.getName();
      }
      return "?";
    }
    for (String t : List.of("v0", "v1", "client")) {
      for (Map<String, Object> c : Json.objs(k.get(t))) {
        try {
          Class<?> x = Class.forName((String) c.get("name"), false, l);
          if (x.getClassLoader() == l && written(x, p.field(), null)) return x.getName();
        } catch (LinkageError | ClassNotFoundException e) {
          // not in this world
        }
      }
    }
    return "?";
  }

  static boolean written(Class<?> c, String name, Object o) throws Exception {
    for (java.lang.reflect.Field f : c.getDeclaredFields()) {
      boolean st = java.lang.reflect.Modifier.isStatic(f.getModifiers());
      if (f.getName().equals(name) && st == (o == null)) {
        f.setAccessible(true);
        if ("put".equals(f.get(o))) return true;
      }
    }
    return false;
  }

  static void call(ClassLoader l, String c) throws Throwable {
    try {
      Class.forName(c, true, l).getMethod("run").invoke(null);
    } catch (InvocationTargetException e) {
      throw e.getCause();
    }
  }

  static URL url(Path p) throws Exception { return p.toUri().toURL(); }
}
