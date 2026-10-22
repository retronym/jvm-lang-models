package pctoy;

import java.util.*;
import pctoy.Core.*;

/** dotc's `InteractiveDriver` under Metals' `CompilerAccess`: every request compiles its unit in a fresh
 * `Run` (the file's earlier symbols unlinked, the whole unit typed, no targeted check), on a shared symbol
 * table. Requests wait in a one-thread LIFO queue; a job that has started is never interrupted (Scala 3
 * has no presentation compiler thread to interrupt, and `Thread.interrupted()` is swallowed at the
 * checkpoints). `CachingDriver` skips the run when the file is the last compiled and unchanged.
 *
 * With `interruptible`, the hypothetical: an interrupt is delivered at a checkpoint, the job unwinds, and
 * `withSharedCompiler` keeps the driver (`InterruptException => default`). */
public final class Scala3Kernel extends Global implements Kernel {
  /** What a session's targeted run types: every declaration up to the one containing the target (the spike's
   * first version), or only that one (`Typer.typedStats` skipping the statements off the path to the target, §2). */
  public enum Targeting { PREFIX, PATH }

  /** The spike's fixes for what targeting and resumption broke, each a finding; off reproduces the bug.
   * `forceSiblingFacts` (I13): a skipped case class gets the typer's burst (`equals`, `hashCode`, `toString`) when
   * its info is asked for. `completeSkippedOnLeave` (I17): before a run of another file, the skipped declarations'
   * signatures are completed in the session's run (`completeSymbolsOf`). `mergeOnReplace` (I22): a declaration
   * replaced after a cancellation is re-indexed with the desugaring that merges a case class into its companion.
   * `typeOffPathWhole` (I21, I25): a nested statement list (a block's, an anonymous template's) is targeted only if the
   * tree that owns it is on the path to the target; one typed off the path, by a completer typing a body ahead, is
   * typed whole. Off, every nested list is targeted while a target is set (`typedBlockStats` before the fix).
   * `inlineBodyWhole` (I28): an inline method's body is never targeted, since its callers inline the typed tree. */
  public record Fixes(boolean forceSiblingFacts, boolean completeSkippedOnLeave, boolean mergeOnReplace, boolean typeOffPathWhole, boolean inlineBodyWhole) {
    public static final Fixes ALL = new Fixes(true, true, true, true, true);
    public static final Fixes NONE = new Fixes(false, false, false, false, false);
  }

  private final String name;
  private final boolean interruptible;
  /** The session: a completion types the file along its target and a later one on the same content resumes
   * the same run (the second spike); `targeting` says how much it types. */
  private final boolean session;
  private final Targeting targeting;
  private final Fixes fixes;
  private Unit sessionUnit;
  private final Deque<Event> queue = new ArrayDeque<>();
  private final List<String> answers = new ArrayList<>();
  private final Map<String, Ast.Source> sources = new LinkedHashMap<>();
  private final Deque<String> toCompile = new ArrayDeque<>();
  private String lastCompiled; private String lastCompiledText;
  private boolean inJob = false, interruptPending = false;

  public Scala3Kernel(String name, boolean interruptible, Scheduler scheduler) { this(name, interruptible, false, scheduler); }

  public Scala3Kernel(String name, boolean interruptible, boolean session, Scheduler scheduler) {
    this(name, interruptible, session, Targeting.PREFIX, Fixes.ALL, scheduler);
  }

  public Scala3Kernel(String name, boolean interruptible, boolean session, Targeting targeting, Fixes fixes, Scheduler scheduler) {
    super(Policy.DOTC, scheduler); this.name = name; this.interruptible = interruptible; this.session = session;
    this.targeting = targeting; this.fixes = fixes;
  }

  @Override protected boolean refusesAcrossRuns() { return true; }

  @Override public String name() { return name; }
  @Override public long work() { return counters.total(); }

  @Override public void reload(List<Ast.Source> ss) {
    for (Ast.Source s : ss) { sources.put(s.name(), s); toCompile.add(s.name()); }
  }

  @Override public void send(Event e) { queue.push(e); }           // LIFO: the newest request first

  @Override protected void onEvent(Event e) { queue.push(e); interruptPending = interruptible && inJob; }
  @Override protected void checkForMoreWork(String where) {}

  /** A checkpoint: the hypothetical interrupt is delivered once, to the job it arrived in. */
  @Override protected void signalDone(Unit unit, String where, Target reached) {
    Event ev = scheduler.at(where);
    if (ev != null) onEvent(ev);
    if (interruptPending) { interruptPending = false; throw new Cancelled("interrupted at " + where); }
  }

  /** `InteractiveDriver.run`: a fresh run of this file. */
  private void run(String file) {
    Ast.Source s = sources.get(file);
    if (file.equals(lastCompiled) && s.text().equals(lastCompiledText) && units.get(file) != null && units.get(file).typed) return;
    inJob = true;
    try {
      Unit u = units.get(file);
      if (session && live(u) && u.source.text().equals(s.text())) {
        List<Integer> all = new ArrayList<>();
        for (int i = 0; i < s.decls().size(); i++) all.add(i);
        typeDecls(u, all);                                 // finish the session's run instead of starting over
      } else {
        leave(file);
        newRun(List.of(s));
        u = units.get(file);
        typeUnit(u, null);
      }
      cleanup(u);
      lastCompiled = file; lastCompiledText = s.text();
    } finally { inJob = false; }
  }

  /** `runUpTo`: type the declaration that contains the target (with `PREFIX`, every one before it too), resuming
   * the session's run when the content is unchanged and the run is still the current one (one `Session` per
   * driver: a run of another file ends it); without a session, the whole file. With `PATH` the target is set for the
   * nested statement lists typed meanwhile (`targetsList`), and the skipped nested statements on its path are resumed. */
  private void runUpTo(String file, String decl, String member) {
    if (!session) { run(file); return; }
    Ast.Source s = sources.get(file);
    int idx = 0;
    for (int i = 0; i < s.decls().size(); i++) if (s.decls().get(i).name().equals(decl)) idx = i;
    inJob = true;
    try {
      Unit u = units.get(file);
      boolean unchanged = u != null && u.source.text().equals(s.text());
      if (unchanged && u.typed && file.equals(lastCompiled)) return;   // CachingDriver: the last whole-file run serves every target
      if (!unchanged || u.typed || !live(u)) {
        leave(file);
        newRun(List.of(s));                                 // content changed, an older whole-file run, or another file's run since: fresh run
        u = units.get(file);
        u.sessionRun = runId; sessionUnit = u;
      }
      List<Integer> idxs = new ArrayList<>();
      for (int i = targeting == Targeting.PREFIX ? 0 : idx; i <= idx; i++) idxs.add(i);
      if (targeting == Targeting.PATH) targetPath = decl + "." + member;
      typeDecls(u, idxs);                                   // resume the session's run; nothing if the target's declaration is typed
      if (targetPath != null) resumeSkipped(u, targetPath); // a target in a skipped nested statement: type it and splice it in
      lastCompiled = file; lastCompiledText = s.text();
    } finally { inJob = false; targetPath = null; }
  }

  /** Nested statement lists are targeted only on the path session (§2's `typedBlockStats`), with the fixes' exceptions. */
  @Override protected boolean targetsList(String owner, boolean inline) {
    if (!session || targeting != Targeting.PATH || targetPath == null) return false;
    if (fixes.inlineBodyWhole && inline) return false;
    if (fixes.typeOffPathWhole && !contains(owner, targetPath)) return false;
    return true;
  }

  /** The session's run is the current run and the unit is not finished: its skipped declarations can be resumed. */
  private boolean live(Unit u) { return u != null && u.sessionRun == runId && !u.typed; }

  /** Before a run of another file (I17): the skipped declarations' signatures are completed in the session's run,
   * since a Namer completer refuses a later run. Bodies stay untyped. */
  private void leave(String file) {
    Unit u = sessionUnit;
    if (u == null || u.name().equals(file) || !live(u) || !fixes.completeSkippedOnLeave) return;
    for (int i = 0; i < u.source.decls().size(); i++) {
      if (u.typedDecls.get(i)) continue;
      ClassInfo ci = classInfo(symOf(u.source.decls().get(i)));
      for (Sym m : ci.decls.syms()) try { typeOf(m); } catch (CyclicReference e) { /* the typer reports it */ }
    }
  }

  private Sym symOf(Ast.Decl d) { return d.isObject() ? toplevel.term(d.name()) : toplevel.type(d.name()); }

  /** I13: a case class whose declaration the session skipped gets its burst when its members are asked for. */
  @Override public ClassInfo classInfo(Sym cls) {
    ClassInfo ci = super.classInfo(cls);
    if (session && fixes.forceSiblingFacts && cls.decl != null && cls.decl.isCase() && !cls.decl.isObject() && !cls.unlinked) {
      Unit u = units.get(cls.file);
      int i = cls.decl.pos();
      if (live(u) && !u.typedDecls.get(i) && u.typing != i) synthesizeAhead(u, cls, ci);
    }
    return ci;
  }

  /** Poisoned statements (I8): a cancellation unwound the typing of `u.typing`, and of any declaration whose
   * symbols it left `Touched`; each is replaced by a fresh parse, re-indexed alone (I22: without the companion
   * merge, unless `mergeOnReplace`), and skipped again. */
  private void recover(Unit u) {
    for (int i = 0; i < u.source.decls().size(); i++) {
      Ast.Decl d = u.source.decls().get(i);
      if (u.typedDecls.get(i) || (i != u.typing && !touched(symOf(d)))) continue;
      enterDecl(u, d);                                       // the same text, so the same tree; a fresh symbol
      if (fixes.mergeOnReplace) {
        Sym cc = toplevel.type(d.name());
        if (cc != null && cc.decl != null && cc.decl.isCase() && cc.file.equals(u.name())) {
          u.synthetics.values().removeIf(p -> p == cc.decl.pos());
          ensureCompanion(u, cc.decl);
        }
      }
    }
    u.typing = -1;
  }

  private static boolean touched(Sym s) {
    if (s == null) return false;
    if (s.locked) return true;
    if (s.info instanceof ClassInfo ci) for (Sym m : ci.decls.syms()) if (m.locked) return true;
    return false;
  }

  /** `InteractiveDriver.cleanup`: a symbol of the unit still lazy after the run gets an error type. */
  private void cleanup(Unit u) {
    for (Sym s : toplevel.syms()) if (s.file.equals(u.name()) && s.info instanceof Completer) s.info = Type.err("unspecified");
  }

  @Override public List<String> drain() {
    while (!toCompile.isEmpty()) job(() -> run(toCompile.poll()), null);
    while (!queue.isEmpty()) {
      Event e = queue.pop();
      switch (e) {
        case Event.Edit ed -> { sources.put(ed.file(), Ast.parse(ed.file(), ed.newText())); job(() -> answers.add(serve(ed.ask())), ed.ask()); }
        case Event.Request rq -> job(() -> answers.add(serve(rq.ask())), rq.ask());
      }
    }
    List<String> r = new ArrayList<>(answers);
    answers.clear();
    return r;
  }

  /** `withSharedCompiler`: an interrupt yields the default answer and keeps the driver. */
  private void job(Runnable thunk, Ask ask) {
    try { thunk.run(); }
    catch (Cancelled c) {
      if (session) for (Unit u : units.values()) if (live(u)) recover(u);
      if (ask != null) answers.add("<interrupted>");
    }
  }

  private String serve(Ask ask) {
    if (!sources.containsKey(ask.file())) return "<no such file>";
    if (ask instanceof Ask.Completion c) runUpTo(c.file(), c.decl(), c.member()); else run(ask.file());
    Unit u = units.get(ask.file());
    return switch (ask) {
      case Ask.Completion c -> completionAnswer(u, new Target(c.decl(), c.member()));
      case Ask.LoadedTyped l -> unitAnswer(u);
    };
  }
}
