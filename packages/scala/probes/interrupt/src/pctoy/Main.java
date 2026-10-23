package pctoy;

import java.nio.file.*;
import java.util.*;

/** `java pctoy.Main <scenarios dir> [--all] [--trace] [--sessions | --tiers | --concurrent] [--kernel name]...` */
public final class Main {
  public static void main(String[] args) throws Exception {
    Path dir = Path.of(args[0]);
    boolean all = false, trace = false, sessions = false, tiers = false, concurrent = false;
    List<String> kernels = new ArrayList<>();
    for (int i = 1; i < args.length; i++) {
      switch (args[i]) {
        case "--all" -> all = true;
        case "--sessions" -> sessions = true;
        case "--tiers" -> tiers = true;
        case "--concurrent" -> concurrent = true;
        case "--trace" -> trace = true;
        case "--kernel" -> kernels.add(args[++i]);
        default -> throw new IllegalArgumentException(args[i]);
      }
    }
    if (kernels.isEmpty()) kernels.addAll(Harness.KERNELS.keySet());
    List<Path> files = new ArrayList<>();
    try (var ds = Files.newDirectoryStream(dir, "*.toy")) { for (Path p : ds) files.add(p); }
    Collections.sort(files);
    final boolean onlyTiers = tiers, onlyConcurrent = concurrent;
    files.removeIf(p -> p.getFileName().toString().startsWith("tier") != onlyTiers);   // the tier scenarios are for --tiers alone
    files.removeIf(p -> p.getFileName().toString().startsWith("concurrent") != onlyConcurrent);   // and the two-reader ones for --concurrent
    if (concurrent) {
      List<String> ks = kernels.isEmpty() || kernels.equals(new ArrayList<>(Harness.KERNELS.keySet())) ? new ArrayList<>(ConcurrentHarness.KERNELS.keySet()) : kernels;
      for (Path p : files) System.out.println(ConcurrentHarness.report(Harness.load(p), ks, all));
      return;
    }
    if (tiers) {
      for (Path p : files) {
        String out = Harness.tiers(Harness.load(p));
        System.out.println(out);
        if (out.contains("DIFFER")) return;
      }
      return;
    }
    if (sessions) {
      List<String> ks = List.of("dotc-session", "dotc-session-path", "dotc-revisions");
      List<String> naive = List.of("dotc-session-naive", "dotc-session-path-naive");
      for (Path p : files) {
        Harness.Scenario sc = Harness.load(p);
        List<Harness.Step> asks = Harness.steps(sc);
        Harness.Replay fresh = Harness.replaySteps(sc, "dotc-metals", asks, false), freshBg = Harness.replaySteps(sc, "dotc-metals", asks, true);
        Map<String, Harness.Replay> bg = new LinkedHashMap<>(), noBg = new LinkedHashMap<>();
        for (String k : ks) { bg.put(k, Harness.replaySteps(sc, k, asks, true)); noBg.put(k, Harness.replaySteps(sc, k, asks, false)); }
        boolean same = fresh.answers().equals(freshBg.answers());
        for (String k : ks) same &= fresh.answers().equals(bg.get(k).answers()) && fresh.answers().equals(noBg.get(k).answers());
        StringBuilder w1 = new StringBuilder(String.format("fresh %3d", freshBg.work())), w2 = new StringBuilder(String.format("fresh %3d", fresh.work()));
        StringBuilder per = new StringBuilder("fresh " + freshBg.perRequest());
        for (String k : ks) {
          String n = k.replace("dotc-", "");
          w1.append(String.format(" %s %3d", n, bg.get(k).work())); w2.append(String.format(" %s %3d", n, noBg.get(k).work()));
          per.append(" ").append(n).append(" ").append(bg.get(k).perRequest());
        }
        System.out.printf("== %-30s %2d requests  work after background: %s   no background: %s   answers %s%n", sc.name(), asks.size(), w1, w2, same ? "same" : "DIFFER");
        System.out.println("   per request after background: " + per);
        if (!same) {
          List<Harness.Replay> others = new ArrayList<>(List.of(freshBg));
          for (String k : ks) { others.add(bg.get(k)); others.add(noBg.get(k)); }
          for (Harness.Replay other : others)
            for (int i = 0; i < asks.size(); i++) if (!fresh.answers().get(i).equals(other.answers().get(i))) {
              System.out.println("   " + asks.get(i) + ":");
              System.out.print(Harness.diff(List.of(fresh.answers().get(i)), List.of(other.answers().get(i))));
              if (!all) return;
            }
          return;
        }
        for (String k : naive) {
          Harness.Replay r = Harness.replaySteps(sc, k, asks, true);
          boolean ok = fresh.answers().equals(r.answers());
          System.out.println("   " + k + " (after background): " + (ok ? "same" : "DIFFER"));
          if (!ok) for (int i = 0; i < asks.size(); i++) if (!fresh.answers().get(i).equals(r.answers().get(i))) {
            System.out.println("    " + asks.get(i) + ":");
            System.out.print(Harness.diff(List.of(fresh.answers().get(i)), List.of(r.answers().get(i))).replaceAll("(?m)^", " "));
          }
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
