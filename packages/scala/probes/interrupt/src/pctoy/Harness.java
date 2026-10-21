package pctoy;

import java.nio.file.*;
import java.util.*;
import pctoy.Core.*;

/** Every interleaving of one event with the background work: the event is injected at each safepoint in
 * turn, and the answers (the event's, then the fully typed units afterwards) are compared with the
 * reference, where the event arrives after the background work is done. */
public final class Harness {
  public record Scenario(String name, List<Ast.Source> sources, Event event, String note) {}

  public interface Factory { Kernel make(Scheduler s); }

  public static final Map<String, Factory> KERNELS = new LinkedHashMap<>();
  static {
    KERNELS.put("scalac-before", s -> new Scala2Kernel("scalac-before", Global.Policy.SCALAC_BEFORE, s));
    KERNELS.put("scalac-after", s -> new Scala2Kernel("scalac-after", Global.Policy.SCALAC_AFTER, s));
    KERNELS.put("scalac-proposed", s -> new Scala2Kernel("scalac-proposed", Global.Policy.SCALAC_PROPOSED, s));
    KERNELS.put("dotc-metals", s -> new Scala3Kernel("dotc-metals", false, s));
    KERNELS.put("dotc-interrupted", s -> new Scala3Kernel("dotc-interrupted", true, s));
    KERNELS.put("psi", s -> new PsiKernel("psi", s));
  }

  /** A scenario file: `// event: <event>` and `// note: ...` lines, then `// file: <Name>` sections and,
   * for an edit, an `// edit: <Name>` section with the new text. Events: `completion F Decl.member`,
   * `loadedTyped F`, `edit F then <event>`. */
  public static Scenario load(Path p) throws java.io.IOException {
    String name = p.getFileName().toString().replaceAll("\\.toy$", "");
    List<String> lines = Files.readAllLines(p);
    String eventLine = null, note = "";
    Map<String, StringBuilder> files = new LinkedHashMap<>(), edits = new LinkedHashMap<>();
    StringBuilder cur = null;
    for (String l : lines) {
      if (l.startsWith("// event:")) eventLine = l.substring(9).trim();
      else if (l.startsWith("// note:")) note = l.substring(8).trim();
      else if (l.startsWith("// file:")) cur = files.computeIfAbsent(l.substring(8).trim(), k -> new StringBuilder());
      else if (l.startsWith("// edit:")) cur = edits.computeIfAbsent(l.substring(8).trim(), k -> new StringBuilder());
      else if (cur != null) cur.append(l).append('\n');
    }
    List<Ast.Source> sources = new ArrayList<>();
    for (Map.Entry<String, StringBuilder> e : files.entrySet()) sources.add(Ast.parse(e.getKey(), e.getValue().toString()));
    return new Scenario(name, sources, parseEvent(eventLine, edits), note);
  }

  private static Event parseEvent(String s, Map<String, StringBuilder> edits) {
    String[] w = s.split("\\s+");
    if (w[0].equals("edit")) {
      String file = w[1];
      String rest = s.substring(s.indexOf("then") + 4).trim();
      Event inner = parseEvent(rest, edits);
      return new Event.Edit(file, edits.get(file).toString(), ((Event.Request) inner).ask());
    }
    return new Event.Request(parseAsk(w));
  }

  private static Ask parseAsk(String[] w) {
    return switch (w[0]) {
      case "completion" -> { String[] dm = w[2].split("\\."); yield new Ask.Completion(w[1], dm[0], dm[1]); }
      case "loadedTyped" -> new Ask.LoadedTyped(w[1]);
      default -> throw new IllegalArgumentException("unknown event " + w[0]);
    };
  }

  public record Result(String kernel, int safepoints, List<String> reference, Map<Integer, List<String>> divergent,
                       Map<Integer, String> firedAt, long referenceWork, double meanWork, List<String> backgroundTrace) {}

  public static Result run(Scenario sc, String kernelName) {
    Factory f = KERNELS.get(kernelName);
    // the background's safepoints
    Scheduler s0 = new Scheduler();
    Kernel probe = f.make(s0);
    s0.reset(-1, null);
    probe.reload(sc.sources());
    probe.drain();
    int K = s0.count;
    List<String> trace = new ArrayList<>(s0.trace());
    // the reference: the event after the background
    Scheduler s1 = new Scheduler();
    Kernel ref = f.make(s1);
    s1.reset(-1, null);
    ref.reload(sc.sources());
    ref.drain();
    List<String> reference = answersFor(ref, sc);
    long refWork = ref.work();
    // every interleaving
    Map<Integer, List<String>> divergent = new LinkedHashMap<>();
    Map<Integer, String> firedAt = new LinkedHashMap<>();
    long totalWork = 0;
    for (int k = 0; k < K; k++) {
      Scheduler s = new Scheduler();
      Kernel kern = f.make(s);
      s.reset(k, sc.event());
      kern.reload(sc.sources());
      List<String> got = new ArrayList<>(kern.drain());
      if (!s.fired) { kern.send(sc.event()); got.addAll(kern.drain()); }
      for (Ast.Source src : sc.sources()) { kern.send(new Event.Request(new Ask.LoadedTyped(src.name()))); got.addAll(kern.drain()); }
      totalWork += kern.work();
      firedAt.put(k, s.fired ? s.trace().get(k) : "<not fired>");
      if (!got.equals(reference)) divergent.put(k, got);
    }
    return new Result(kernelName, K, reference, divergent, firedAt, refWork, K == 0 ? 0 : (double) totalWork / K, trace);
  }

  private static List<String> answersFor(Kernel k, Scenario sc) {
    List<String> r = new ArrayList<>();
    k.send(sc.event());
    r.addAll(k.drain());
    for (Ast.Source src : sc.sources()) { k.send(new Event.Request(new Ask.LoadedTyped(src.name()))); r.addAll(k.drain()); }
    return r;
  }

  public static String diff(List<String> reference, List<String> got) {
    StringBuilder b = new StringBuilder();
    int n = Math.max(reference.size(), got.size());
    for (int i = 0; i < n; i++) {
      String a = i < reference.size() ? reference.get(i) : "<missing>", c = i < got.size() ? got.get(i) : "<missing>";
      if (a.equals(c)) continue;
      b.append("    answer ").append(i + 1).append(":\n");
      Set<String> al = new LinkedHashSet<>(List.of(a.split("\n"))), cl = new LinkedHashSet<>(List.of(c.split("\n")));
      for (String l : al) if (!cl.contains(l)) b.append("      - ").append(l).append('\n');
      for (String l : cl) if (!al.contains(l)) b.append("      + ").append(l).append('\n');
    }
    return b.toString();
  }
}
