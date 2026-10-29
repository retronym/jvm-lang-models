package pctoy;

import java.util.*;
import pctoy.Core.*;

/** Two requests on the concurrent kernel, interleaved at every pair of safepoints: the first reader runs alone to
 * its `i`th safepoint, the second to its `j`th, and from there they alternate a safepoint at a time (a reader waiting
 * on the other's barrier is skipped) until both have answered; the harness then types the rest of each unit. The
 * answers (both readers', then each unit) are compared with the reference, where the first reader runs to its answer
 * before the second starts. A divergence whose every differing answer reports a cyclic reference on both sides is a
 * cycle reported at another site, which the design accepts (§4.2); one whose differing answers report a cyclic
 * reference the reference does not have is a false cycle (I54, I87); any other is a race.
 *
 * A scenario with `// cancel: A` adds a third dimension: for every pair, the first reader is cancelled at each of its
 * safepoints in turn, the abort of §3.1 with a waiter. Its own answer is then `<cancelled>` and not compared; the
 * second reader's and the units' must still be the reference's. The aborts of the `VICTIM` rule (a reader aborted at
 * a wait-for cycle and retried) are counted per pair, and a pair where a reader hit the retry bound is a livelock. */
public final class ConcurrentHarness {
  public interface Factory { ConcurrentKernel make(Scheduler s); }

  public static final Map<String, Factory> KERNELS = new LinkedHashMap<>();
  static {
    KERNELS.put("dotc-concurrent", s -> new ConcurrentKernel("dotc-concurrent", ConcurrentKernel.PeekMode.OWN, true, s));
    KERNELS.put("dotc-concurrent-peek-any", s -> new ConcurrentKernel("dotc-concurrent-peek-any", ConcurrentKernel.PeekMode.ANY, true, s));
    KERNELS.put("dotc-concurrent-shared-scratch", s -> new ConcurrentKernel("dotc-concurrent-shared-scratch", ConcurrentKernel.PeekMode.OWN, false, s));
    KERNELS.put("dotc-concurrent-victim", roots("dotc-concurrent-victim", ConcurrentKernel.RootMode.FACT, ConcurrentKernel.CycleRule.VICTIM, true));
    KERNELS.put("dotc-concurrent-root-pair", roots("dotc-concurrent-root-pair", ConcurrentKernel.RootMode.PAIR, ConcurrentKernel.CycleRule.RAISE, true));
    KERNELS.put("dotc-concurrent-root-pair-victim", roots("dotc-concurrent-root-pair-victim", ConcurrentKernel.RootMode.PAIR, ConcurrentKernel.CycleRule.VICTIM, true));
    KERNELS.put("dotc-concurrent-root-file", roots("dotc-concurrent-root-file", ConcurrentKernel.RootMode.FILE, ConcurrentKernel.CycleRule.RAISE, true));
    KERNELS.put("dotc-concurrent-root-file-victim", roots("dotc-concurrent-root-file-victim", ConcurrentKernel.RootMode.FILE, ConcurrentKernel.CycleRule.VICTIM, true));
    KERNELS.put("dotc-concurrent-root-file-leak", roots("dotc-concurrent-root-file-leak", ConcurrentKernel.RootMode.FILE, ConcurrentKernel.CycleRule.VICTIM, false));
  }

  private static Factory roots(String name, ConcurrentKernel.RootMode roots, ConcurrentKernel.CycleRule rule, boolean scratchFinally) {
    return s -> new ConcurrentKernel(name, ConcurrentKernel.PeekMode.OWN, true, roots, rule, scratchFinally, s);
  }

  /** One interleaving: the answers, each reader's safepoint trace, whether the scheduler found a deadlock, how many
   * times a reader was aborted as a cycle's victim, and whether one hit the retry bound. */
  public record Outcome(List<String> answers, List<String> traceA, List<String> traceB, boolean deadlock, int aborts, boolean livelock) {}

  public record Result(String kernel, int safepointsA, int safepointsB, int cancels, Outcome reference, Map<String, Outcome> divergent,
                       Set<String> cycleSite, Set<String> falseCycle, Set<String> deadlocked, Map<String, Integer> aborts, Set<String> livelocked,
                       boolean referenceIsSequentialKernel, List<String> sequentialKernel) {
    public int races() { return divergent.size() - cycleSite.size() - falseCycle.size(); }
    public int totalAborts() { int n = 0; for (int a : aborts.values()) n += a; return n; }
  }

  /** Run the schedule `(i, j)`, cancelling the first reader at its `cancelA`th safepoint (0: never); `i < 0`: the first
   * reader to completion before the second starts (the reference). */
  public static Outcome run(Harness.Scenario sc, String kernelName, int i, int j, int cancelA) {
    ConcurrentKernel k = KERNELS.get(kernelName).make(new Scheduler());
    k.reload(sc.sources());
    ConcurrentKernel.Sched sched = k.sched;
    ConcurrentKernel.Reader a = sched.reader("A", sc.concurrent().get(0)), b = sched.reader("B", sc.concurrent().get(1));
    a.cancelAt = cancelA;
    sched.start(a); sched.start(b);
    if (i < 0) {
      while (a.state == ConcurrentKernel.State.RUNNABLE) sched.turn(a);
    } else {
      while (a.state == ConcurrentKernel.State.RUNNABLE && a.safepoints < i) sched.turn(a);
      while (b.state == ConcurrentKernel.State.RUNNABLE && b.safepoints < j) sched.turn(b);
    }
    boolean deadlock = false;
    ConcurrentKernel.Reader next = a;
    while (!sched.allDone()) {
      ConcurrentKernel.Reader other = next == a ? b : a;
      if (next.state == ConcurrentKernel.State.RUNNABLE) sched.turn(next);
      else if (other.state == ConcurrentKernel.State.RUNNABLE) sched.turn(other);
      else {                                                   // both waiting: a deadlock the cycle check missed
        deadlock = true; sched.deadlock = true;
        for (ConcurrentKernel.Reader r : sched.readers) if (r.state != ConcurrentKernel.State.DONE) { r.state = ConcurrentKernel.State.RUNNABLE; sched.turn(r); }
        break;
      }
      next = other;
    }
    sched.current = null;
    List<String> answers = new ArrayList<>(List.of(a.answer, b.answer));
    for (Ast.Source s : sc.sources()) {
      Global.Unit u = k.units.get(s.name());
      try { k.finish(u); answers.add(k.unitAnswer(u)); }
      catch (RuntimeException e) { answers.add("<failed: " + e.getMessage() + ">"); }   // an UnpicklingError fails the whole-unit request too
    }
    return new Outcome(answers, new ArrayList<>(a.trace), new ArrayList<>(b.trace), deadlock, a.aborts + b.aborts, a.livelock || b.livelock);
  }

  private static boolean cyclic(String s) { return s.contains("cyclic reference"); }

  public static Result run(Harness.Scenario sc, String kernelName) {
    Outcome ref = run(sc, kernelName, -1, 0, 0);
    Outcome refB = run(sc, kernelName, 0, Integer.MAX_VALUE, 0);   // the second reader alone first: its safepoint count
    int ka = ref.traceA().size(), kb = refB.traceB().size();
    boolean cancel = sc.cancel() != null;
    int cancels = cancel ? ka : 0;
    Map<String, Outcome> divergent = new LinkedHashMap<>();
    Set<String> cycleSite = new LinkedHashSet<>(), falseCycle = new LinkedHashSet<>(), deadlocked = new LinkedHashSet<>(), livelocked = new LinkedHashSet<>();
    Map<String, Integer> aborts = new LinkedHashMap<>();
    for (int i = 0; i <= ka; i++) for (int j = 0; j <= kb; j++) for (int c = cancel ? 1 : 0; c <= cancels; c++) {
      Outcome o = run(sc, kernelName, i, j, c);
      String key = i + "," + j + (cancel ? "@" + c : "");
      if (o.deadlock()) deadlocked.add(key);
      if (o.aborts() > 0) aborts.put(key, o.aborts());
      if (o.livelock()) livelocked.add(key);
      List<String> got = new ArrayList<>(o.answers());
      if (got.get(0).equals("<cancelled>")) got.set(0, ref.answers().get(0));   // the cancelled reader has no answer to compare
      if (!got.equals(ref.answers())) {
        divergent.put(key, o);
        boolean cyc = true, falseCyc = true, refHasNone = false;
        for (int n = 0; n < got.size(); n++) {
          String x = ref.answers().get(n), y = got.get(n);
          if (x.equals(y)) continue;
          if (!(cyclic(x) && cyclic(y))) cyc = false;
          if (!cyclic(y)) falseCyc = false;
          if (!cyclic(x)) refHasNone = true;
        }
        if (cyc) cycleSite.add(key);
        else if (falseCyc && refHasNone) falseCycle.add(key);
      }
    }
    List<Harness.Step> steps = new ArrayList<>();
    for (Ask ask : sc.concurrent()) steps.add(new Harness.Step(new Event.Request(ask), -1));
    for (Ast.Source s : sc.sources()) steps.add(new Harness.Step(new Event.Request(new Ask.LoadedTyped(s.name())), -1));
    List<String> seq = Harness.replaySteps(sc, "dotc-session-path", steps, false).answers();
    return new Result(kernelName, ka, kb, cancels, ref, divergent, cycleSite, falseCycle, deadlocked, aborts, livelocked, seq.equals(ref.answers()), seq);
  }

  /** A list of schedule keys, cut after 40: the cancel dimension makes hundreds. */
  private static String keys(Collection<String> ks) {
    if (ks.size() <= 40) return ks.toString();
    List<String> head = new ArrayList<>(ks).subList(0, 40);
    return head.toString().replaceFirst("]$", ", ... " + (ks.size() - 40) + " more]");
  }

  private static void example(StringBuilder b, Result r, String key, String kind) {
    Outcome o = r.divergent().get(key);
    b.append("    (i,j)=").append(key).append(' ').append(kind).append(":\n");
    b.append("      A: ").append(String.join(", ", o.traceA())).append('\n');
    b.append("      B: ").append(String.join(", ", o.traceB())).append('\n');
    b.append(Harness.diff(r.reference().answers(), o.answers()).replaceAll("(?m)^", "  "));
  }

  public static String report(Harness.Scenario sc, Collection<String> kernels, boolean all) {
    StringBuilder b = new StringBuilder();
    b.append("== ").append(sc.name()).append(": ").append(sc.concurrent().get(0)).append(" | ").append(sc.concurrent().get(1));
    if (sc.cancel() != null) b.append(" | cancel ").append(sc.cancel()).append(" at each safepoint");
    b.append('\n');
    if (!sc.note().isEmpty()) b.append("   ").append(sc.note()).append('\n');
    b.append(String.format("   %-32s %10s %10s %12s %12s %10s %8s %8s   %s%n", "kernel", "pairs", "races", "cycle site", "false cycle", "deadlock", "aborts", "livelock", "A then B = dotc-session-path"));
    List<Result> results = new ArrayList<>();
    for (String k : kernels) {
      Result r = run(sc, k);
      results.add(r);
      int pairs = (r.safepointsA() + 1) * (r.safepointsB() + 1);
      String space = pairs + " (" + r.safepointsA() + "x" + r.safepointsB() + ")" + (r.cancels() > 0 ? " x" + r.cancels() : "");
      b.append(String.format("   %-32s %10s %10d %12d %12d %10d %8d %8d   %s%n", k, space, r.races(), r.cycleSite().size(), r.falseCycle().size(),
          r.deadlocked().size(), r.totalAborts(), r.livelocked().size(), r.referenceIsSequentialKernel() ? "same" : "DIFFER"));
    }
    for (Result r : results) {
      if (!r.referenceIsSequentialKernel()) {
        b.append("   ").append(r.kernel()).append(" A then B differs from dotc-session-path:\n");
        b.append(Harness.diff(r.sequentialKernel(), r.reference().answers()).replaceAll("(?m)^", "  "));
      }
      if (!r.aborts().isEmpty()) {
        List<String> xs = new ArrayList<>();
        for (Map.Entry<String, Integer> e : r.aborts().entrySet()) xs.add(e.getKey() + (e.getValue() > 1 ? ":" + e.getValue() : ""));
        b.append("   ").append(r.kernel()).append(" aborts a victim at (i,j) = ").append(keys(xs)).append('\n');
        if (!r.livelocked().isEmpty()) b.append("   ").append(r.kernel()).append(" hits the retry bound at (i,j) = ").append(keys(r.livelocked())).append('\n');
      }
      if (r.divergent().isEmpty()) continue;
      List<String> races = new ArrayList<>(r.divergent().keySet()); races.removeAll(r.cycleSite()); races.removeAll(r.falseCycle());
      if (!races.isEmpty()) b.append("   ").append(r.kernel()).append(" races at (i,j) = ").append(keys(races)).append('\n');
      if (!r.cycleSite().isEmpty()) b.append("   ").append(r.kernel()).append(" reports the cycle elsewhere at (i,j) = ").append(keys(r.cycleSite())).append('\n');
      if (!r.falseCycle().isEmpty()) b.append("   ").append(r.kernel()).append(" reports a false cycle at (i,j) = ").append(keys(r.falseCycle())).append('\n');
      int shown = 0;
      for (String key : r.divergent().keySet()) {                // one race, or two cycle sites, unless --all
        if (r.falseCycle().contains(key)) continue;
        boolean race = !r.cycleSite().contains(key);
        if (!all && shown > 0 && (race || !races.isEmpty())) continue;
        if (!all && !race && shown > 1) continue;
        example(b, r, key, race ? "race" : "cycle site");
        shown++;
        if (!all && shown >= 2) break;
      }
      for (String key : r.falseCycle()) { example(b, r, key, "false cycle"); if (!all) break; }
    }
    b.append("   reference (A then B):\n");
    for (int i = 0; i < results.get(0).reference().answers().size(); i++)
      b.append("    answer ").append(i + 1).append(": ").append(results.get(0).reference().answers().get(i).replace("\n", "\n              ").trim()).append('\n');
    return b.toString();
  }
}
