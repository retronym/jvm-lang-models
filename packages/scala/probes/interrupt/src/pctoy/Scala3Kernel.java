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
  private final String name;
  private final boolean interruptible;
  private final Deque<Event> queue = new ArrayDeque<>();
  private final List<String> answers = new ArrayList<>();
  private final Map<String, Ast.Source> sources = new LinkedHashMap<>();
  private final Deque<String> toCompile = new ArrayDeque<>();
  private String lastCompiled; private String lastCompiledText;
  private boolean inJob = false, interruptPending = false;

  public Scala3Kernel(String name, boolean interruptible, Scheduler scheduler) {
    super(Policy.DOTC, scheduler); this.name = name; this.interruptible = interruptible;
  }

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
      newRun(List.of(s));
      Unit u = units.get(file);
      typeUnit(u, null);
      cleanup(u);
      lastCompiled = file; lastCompiledText = s.text();
    } finally { inJob = false; }
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
    catch (Cancelled c) { if (ask != null) answers.add("<interrupted>"); }
  }

  private String serve(Ask ask) {
    if (!sources.containsKey(ask.file())) return "<no such file>";
    run(ask.file());
    Unit u = units.get(ask.file());
    return switch (ask) {
      case Ask.Completion c -> completionAnswer(u, new Target(c.decl(), c.member()));
      case Ask.LoadedTyped l -> unitAnswer(u);
    };
  }
}
