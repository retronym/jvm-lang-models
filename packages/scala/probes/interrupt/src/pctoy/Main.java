package pctoy;

import java.nio.file.*;
import java.util.*;

/** `java pctoy.Main <scenarios dir> [--all] [--trace] [--kernel name]...` */
public final class Main {
  public static void main(String[] args) throws Exception {
    Path dir = Path.of(args[0]);
    boolean all = false, trace = false, sessions = false;
    List<String> kernels = new ArrayList<>();
    for (int i = 1; i < args.length; i++) {
      switch (args[i]) {
        case "--all" -> all = true;
        case "--sessions" -> sessions = true;
        case "--trace" -> trace = true;
        case "--kernel" -> kernels.add(args[++i]);
        default -> throw new IllegalArgumentException(args[i]);
      }
    }
    if (kernels.isEmpty()) kernels.addAll(Harness.KERNELS.keySet());
    List<Path> files = new ArrayList<>();
    try (var ds = Files.newDirectoryStream(dir, "*.toy")) { for (Path p : ds) files.add(p); }
    Collections.sort(files);
    if (sessions) {
      for (Path p : files) {
        Harness.Scenario sc = Harness.load(p);
        List<Core.Event> asks = Harness.sweep(sc);
        Harness.Replay freshBg = Harness.replay(sc, "dotc-metals", asks, true), sessBg = Harness.replay(sc, "dotc-session", asks, true);
        Harness.Replay fresh = Harness.replay(sc, "dotc-metals", asks, false);
        Harness.Replay sess = Harness.replay(sc, "dotc-session", asks, false);
        boolean same = fresh.answers().equals(sess.answers()) && freshBg.answers().equals(sessBg.answers()) && fresh.answers().equals(freshBg.answers());
        System.out.printf("== %-30s %2d requests  work after background: fresh %3d session %3d   no background: fresh %3d session %3d   answers %s%n",
            sc.name(), asks.size(), freshBg.work(), sessBg.work(), fresh.work(), sess.work(), same ? "same" : "DIFFER");
        if (!same) for (int i = 0; i < asks.size(); i++) if (!fresh.answers().get(i).equals(sess.answers().get(i))) {
          System.out.println("   " + asks.get(i) + ":");
          System.out.print(Harness.diff(List.of(fresh.answers().get(i)), List.of(sess.answers().get(i))));
          if (!all) break;
        }
      }
      return;
    }
    for (Path p : files) {
      Harness.Scenario sc = Harness.load(p);
      System.out.println("== " + sc.name() + ": " + sc.event() + (sc.note().isEmpty() ? "" : "\n   " + sc.note()));
      System.out.printf("   %-17s %10s %10s %14s%n", "kernel", "safepoints", "divergent", "work ref/mean");
      List<Harness.Result> results = new ArrayList<>();
      for (String k : kernels) {
        Harness.Result r = Harness.run(sc, k);
        results.add(r);
        System.out.printf("   %-17s %10d %10s %14s%n", k, r.safepoints(), r.divergent().size() + "/" + r.safepoints(), r.referenceWork() + "/" + String.format("%.1f", r.meanWork()));
      }
      for (Harness.Result r : results) {
        if (trace) System.out.println("   " + r.kernel() + " background safepoints: " + String.join(", ", r.backgroundTrace()));
        if (r.divergent().isEmpty()) continue;
        System.out.println("   " + r.kernel() + " diverges at k = " + r.divergent().keySet());
        for (Map.Entry<Integer, List<String>> e : r.divergent().entrySet()) {
          System.out.println("    k=" + e.getKey() + " (event at '" + r.firedAt().get(e.getKey()) + "'):");
          System.out.print(Harness.diff(r.reference(), e.getValue()));
          if (!all) { int more = r.divergent().size() - 1; if (more > 0) System.out.println("    ... " + more + " more (--all)"); break; }
        }
      }
      System.out.println("   reference:");
      for (int i = 0; i < results.get(0).reference().size(); i++) {
        String a = results.get(0).reference().get(i);
        System.out.println("    answer " + (i + 1) + ": " + a.replace("\n", "\n              ").trim());
      }
      System.out.println();
    }
  }
}
