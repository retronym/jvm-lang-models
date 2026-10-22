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
    KERNELS.put("dotc-metals", s -> new Scala3Kernel("dotc-metals", false, s));
    KERNELS.put("dotc-session", s -> new Scala3Kernel("dotc-session", false, true, s));
    KERNELS.put("dotc-interrupted", s -> new Scala3Kernel("dotc-interrupted", true, s));
    KERNELS.put("psi", s -> new PsiKernel("psi", s));
  }
  /** Kernels for replays only: no safepoints, so no interleavings to sweep. */
  public static final Map<String, Factory> REPLAY_KERNELS = Map.of("dotc-revisions", s -> new Revisions("dotc-revisions", s));

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

  /** A request sequence on a kernel, after the background: the answers, the work, and the work of each request. */
  public record Replay(List<String> answers, long work, List<Long> perRequest) {}

  public static Replay replay(Scenario sc, String kernelName, List<Event> events, boolean background) {
    Scheduler s = new Scheduler();
    Kernel k = KERNELS.getOrDefault(kernelName, REPLAY_KERNELS.get(kernelName)).make(s);
    s.reset(-1, null);
    k.reload(sc.sources());
    if (background) k.drain();
    long w0 = k.work();
    List<String> answers = new ArrayList<>();
    List<Long> per = new ArrayList<>();
    for (Event e : events) { long w = k.work(); k.send(e); answers.addAll(k.drain()); per.add(k.work() - w); }
    return new Replay(answers, k.work() - w0, per);
  }

  /** Stage 3's tiers: the units typed whole on `dotc-revisions`, then the scenario's edit and its request; which facts
   * the request recomputed (changed or backdated) and which it reused, checked: a fact was recomputed iff its old trace
   * holds a fact that changed since it was verified (dependents by trace), and per tier, `tier1` recomputes one typed
   * form, `tier2` changes the edited member's type, `tier3` recomputes every top-level lookup it re-validates. The
   * answers must be the fresh-run kernel's. */
  public static String tiers(Scenario sc) {
    StringBuilder b = new StringBuilder("== " + sc.name() + ": " + sc.event() + "\n   " + sc.note() + "\n");
    Revisions k = new Revisions("dotc-revisions", new Scheduler());
    k.reload(sc.sources());
    k.drain();
    Map<Revisions.Fact, List<Revisions.Fact>> traces = new HashMap<>();
    Map<Revisions.Fact, Integer> verified = new HashMap<>();
    for (Revisions.Fact f : k.facts()) if (!f.isInput()) { traces.put(f, f.trace); verified.put(f, f.verifiedAt); }
    k.recomputed.clear();
    k.send(sc.event());
    List<String> got = k.drain();
    List<String> fresh = replay(sc, "dotc-metals", List.of(sc.event()), true).answers();
    int r = k.rev;
    List<String> inputs = new ArrayList<>(), rec = new ArrayList<>(), fresh_ = new ArrayList<>(), reused = new ArrayList<>(), bad = new ArrayList<>();
    for (Revisions.Fact f : k.facts()) {
      if (f.isInput()) { if (f.changedAt == r) inputs.add(f.key); continue; }
      if (f.verifiedAt != r) continue;
      boolean ran = k.recomputed.contains(f);
      if (!traces.containsKey(f)) { fresh_.add(f.key); continue; }
      boolean dep = traces.get(f).stream().anyMatch(d -> d.changedAt > verified.get(f));
      if (ran != dep) bad.add(f.key + (ran ? " recomputed without a changed dep" : " reused with a changed dep"));
      if (ran) rec.add(f.key + (f.changedAt == r ? " (changed)" : " (backdated)")); else reused.add(f.key);
    }
    long typed = k.recomputed.stream().filter(f -> f.key.startsWith("typed ") && traces.containsKey(f)).count();
    String tier = sc.name().substring(0, 5);
    switch (tier) {
      case "tier1" -> { if (typed != 1) bad.add(typed + " typed forms recomputed, not 1"); }
      case "tier2" -> {
        for (String in : inputs) if (in.startsWith("member ") && !rec.contains("type " + in.substring(7) + " (changed)")) bad.add("type " + in.substring(7) + " not changed");
      }
      default -> {
        for (Revisions.Fact f : k.facts())
          if (f.key.startsWith("lookup <toplevel>") && f.verifiedAt == r && traces.containsKey(f) && !k.recomputed.contains(f)) bad.add(f.key + " not recomputed");
      }
    }
    b.append("   inputs changed: ").append(String.join(", ", inputs)).append('\n');
    b.append("   recomputed ").append(rec.size()).append(": ").append(String.join(", ", rec)).append('\n');
    b.append("   new ").append(fresh_.size()).append(": ").append(String.join(", ", fresh_)).append('\n');
    b.append("   reused ").append(reused.size()).append(": ").append(String.join(", ", reused)).append('\n');
    b.append("   ").append(tier).append(" check: ").append(bad.isEmpty() ? "ok" : "FAILED " + bad).append('\n');
    b.append("   answers: ").append(got.equals(fresh) ? "same as dotc-metals" : "DIFFER\n" + diff(fresh, got)).append('\n');
    return b.toString();
  }

  /** An editing session on the scenario's first file: a completion at its first inferred member, then three times an
   * edit at the end of the file (a class appended) followed by the same completion, then a completion at the last
   * inferred member, then the unit. A targeted session types the prefix per edit; a whole-file run types everything. */
  public static List<Event> sweep(Scenario sc) {
    Ast.Source src = sc.sources().get(0);
    Ask first = null, last = null;
    for (Ast.Decl d : src.decls()) for (Ast.Member m : d.members()) if (m.inferred()) {
      Ask a = new Ask.Completion(src.name(), d.name(), m.name());
      if (first == null) first = a;
      last = a;
    }
    List<Event> events = new ArrayList<>();
    if (first == null) return List.of(new Event.Request(new Ask.LoadedTyped(src.name())));
    events.add(new Event.Request(first));
    String text = src.text();
    for (int k = 1; k <= 3; k++) {
      text = text + "\nclass Edited" + k + " {}\n";
      events.add(new Event.Edit(src.name(), text, first));
    }
    events.add(new Event.Request(last));
    events.add(new Event.Request(new Ask.LoadedTyped(src.name())));
    return events;
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
