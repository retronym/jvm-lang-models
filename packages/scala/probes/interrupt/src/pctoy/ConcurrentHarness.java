package pctoy;

import java.util.*;
import pctoy.Core.*;

/** Two requests on the concurrent kernel, interleaved at every pair of safepoints: the first reader runs alone to
 * its `i`th safepoint, the second to its `j`th, and from there they alternate a safepoint at a time (a reader waiting
 * on the other's barrier is skipped) until both have answered; the harness then types the rest of each unit. The
 * answers (both readers', then each unit) are compared with the reference, where the first reader runs to its answer
 * before the second starts. A divergence whose every differing answer reports a cyclic reference on both sides is a
 * cycle reported at another site, which the design accepts (§4.2); any other is a race. */
public final class ConcurrentHarness {
  public interface Factory { ConcurrentKernel make(Scheduler s); }

  public static final Map<String, Factory> KERNELS = new LinkedHashMap<>();
  static {
    KERNELS.put("dotc-concurrent", s -> new ConcurrentKernel("dotc-concurrent", ConcurrentKernel.PeekMode.OWN, true, s));
    KERNELS.put("dotc-concurrent-peek-any", s -> new ConcurrentKernel("dotc-concurrent-peek-any", ConcurrentKernel.PeekMode.ANY, true, s));
    KERNELS.put("dotc-concurrent-shared-scratch", s -> new ConcurrentKernel("dotc-concurrent-shared-scratch", ConcurrentKernel.PeekMode.OWN, false, s));
  }

  /** One interleaving: the answers, each reader's safepoint trace, and whether the scheduler found a deadlock. */
  public record Outcome(List<String> answers, List<String> traceA, List<String> traceB, boolean deadlock) {}

  public record Result(String kernel, int safepointsA, int safepointsB, Outcome reference, Map<String, Outcome> divergent,
                       Set<String> cycleSite, Set<String> deadlocked, boolean referenceIsSequentialKernel, List<String> sequentialKernel) {}

  /** Run the schedule `(i, j)`; `i < 0`: the first reader to completion before the second starts (the reference). */
  public static Outcome run(Harness.Scenario sc, String kernelName, int i, int j) {
    ConcurrentKernel k = KERNELS.get(kernelName).make(new Scheduler());
    k.reload(sc.sources());
    ConcurrentKernel.Sched sched = k.sched;
    ConcurrentKernel.Reader a = sched.reader("A", sc.concurrent().get(0)), b = sched.reader("B", sc.concurrent().get(1));
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
    for (Ast.Source s : sc.sources()) { Global.Unit u = k.units.get(s.name()); k.finish(u); answers.add(k.unitAnswer(u)); }
    return new Outcome(answers, new ArrayList<>(a.trace), new ArrayList<>(b.trace), deadlock);
  }

  public static Result run(Harness.Scenario sc, String kernelName) {
    Outcome ref = run(sc, kernelName, -1, 0);
    Outcome refB = run(sc, kernelName, 0, Integer.MAX_VALUE);   // the second reader alone first: its safepoint count
    int ka = ref.traceA().size(), kb = refB.traceB().size();
    Map<String, Outcome> divergent = new LinkedHashMap<>();
    Set<String> cycleSite = new LinkedHashSet<>(), deadlocked = new LinkedHashSet<>();
    for (int i = 0; i <= ka; i++) for (int j = 0; j <= kb; j++) {
      Outcome o = run(sc, kernelName, i, j);
      String key = i + "," + j;
      if (o.deadlock()) deadlocked.add(key);
      if (!o.answers().equals(ref.answers())) {
        divergent.put(key, o);
        boolean cyc = true;
        for (int n = 0; n < o.answers().size(); n++) {
          String x = ref.answers().get(n), y = o.answers().get(n);
          if (!x.equals(y) && !(x.contains("cyclic reference") && y.contains("cyclic reference"))) cyc = false;
        }
        if (cyc) cycleSite.add(key);
      }
    }
    List<Harness.Step> steps = new ArrayList<>();
    for (Ask ask : sc.concurrent()) steps.add(new Harness.Step(new Event.Request(ask), -1));
    for (Ast.Source s : sc.sources()) steps.add(new Harness.Step(new Event.Request(new Ask.LoadedTyped(s.name())), -1));
    List<String> seq = Harness.replaySteps(sc, "dotc-session-path", steps, false).answers();
    return new Result(kernelName, ka, kb, ref, divergent, cycleSite, deadlocked, seq.equals(ref.answers()), seq);
  }

  public static String report(Harness.Scenario sc, Collection<String> kernels, boolean all) {
    StringBuilder b = new StringBuilder();
    b.append("== ").append(sc.name()).append(": ").append(sc.concurrent().get(0)).append(" | ").append(sc.concurrent().get(1)).append('\n');
    if (!sc.note().isEmpty()) b.append("   ").append(sc.note()).append('\n');
    b.append(String.format("   %-32s %10s %10s %12s %10s   %s%n", "kernel", "pairs", "divergent", "cycle site", "deadlock", "A then B = dotc-session-path"));
    List<Result> results = new ArrayList<>();
    for (String k : kernels) {
      Result r = run(sc, k);
      results.add(r);
      int pairs = (r.safepointsA() + 1) * (r.safepointsB() + 1);
      b.append(String.format("   %-32s %10s %10d %12d %10d   %s%n", k, pairs + " (" + r.safepointsA() + "x" + r.safepointsB() + ")",
          r.divergent().size() - r.cycleSite().size(), r.cycleSite().size(), r.deadlocked().size(), r.referenceIsSequentialKernel() ? "same" : "DIFFER"));
    }
    for (Result r : results) {
      if (!r.referenceIsSequentialKernel()) {
        b.append("   ").append(r.kernel()).append(" A then B differs from dotc-session-path:\n");
        b.append(Harness.diff(r.sequentialKernel(), r.reference().answers()).replaceAll("(?m)^", "  "));
      }
      if (r.divergent().isEmpty()) continue;
      List<String> races = new ArrayList<>(r.divergent().keySet()); races.removeAll(r.cycleSite());
      if (!races.isEmpty()) b.append("   ").append(r.kernel()).append(" races at (i,j) = ").append(races).append('\n');
      if (!r.cycleSite().isEmpty()) b.append("   ").append(r.kernel()).append(" reports the cycle elsewhere at (i,j) = ").append(r.cycleSite()).append('\n');
      int shown = 0;
      for (Map.Entry<String, Outcome> e : r.divergent().entrySet()) {
        boolean race = !r.cycleSite().contains(e.getKey());
        if (!all && shown > 0 && (race || !races.isEmpty())) continue;   // one of each kind unless --all
        if (!all && !race && shown > 1) continue;
        b.append("    (i,j)=").append(e.getKey()).append(race ? " race" : " cycle site").append(":\n");
        b.append("      A: ").append(String.join(", ", e.getValue().traceA())).append('\n');
        b.append("      B: ").append(String.join(", ", e.getValue().traceB())).append('\n');
        b.append(Harness.diff(r.reference().answers(), e.getValue().answers()).replaceAll("(?m)^", "  "));
        shown++;
        if (!all && shown >= 2) break;
      }
    }
    b.append("   reference (A then B):\n");
    for (int i = 0; i < results.get(0).reference().answers().size(); i++)
      b.append("    answer ").append(i + 1).append(": ").append(results.get(0).reference().answers().get(i).replace("\n", "\n              ").trim()).append('\n');
    return b.toString();
  }
}
