package pctoy;

import java.util.*;
import java.util.concurrent.Semaphore;
import pctoy.Core.*;

/** dotc's session with two readers at once, as the multi-reader design proposes (`interactive-multi-reader.md`
 * §3.1, §4): one run over the loaded sources, and each request a reader that types the declaration containing its
 * target (the path session's `runUpTo`) on a thread of its own. The symbol table's black hole gets an owner: a
 * completer in progress is seen by the reader completing it (a re-entry is a `CyclicReference`, as today); any other
 * reader that needs the fact waits on its barrier until the owner publishes or unwinds, and an unwound completion
 * leaves the symbol completable, so the waiter takes it over. A wait that would close a wait-for cycle between the
 * two readers (the other reader is waiting on a fact this one holds) is a `CyclicReference` in the reader that
 * closes it (§4.2). A declaration being typed is a fact with a barrier too (§3.2): a reader whose target is in a
 * declaration the other reader is typing waits for it.
 *
 * The readers are real threads, but only one runs at a time: every safepoint of the typer (`signalDone`) hands
 * control back to the harness's scheduler, which picks the next reader, so an interleaving is a deterministic
 * function of the schedule, as Lincheck's model checker makes it. A reader's scratch that `Global` keeps in a
 * field (the request's `targetPath`, kind A of the design's table) is saved and restored at each switch: the
 * `Reader` of plan step 2, in miniature.
 *
 * `peek` is the toy's `isCompleting` (§4.1): `findImplicit` skips a view whose member is being completed, as
 * scalac's implicit search skips a `LOCKED` candidate. With `PeekMode.ANY` "being completed" means by either
 * reader, and the answer depends on the schedule; with `OWN` it means by this reader, and a member in progress on
 * the other reader is waited for like any other fact. */
public final class ConcurrentKernel extends Global {
  public enum PeekMode { OWN, ANY }

  private final String name;
  private final PeekMode peekMode;
  /** Save and restore the per-request scratch at a switch; off, the two readers share `targetPath` (kind A). */
  private final boolean readerScratch;
  private final Map<String, Ast.Source> sources = new LinkedHashMap<>();

  public ConcurrentKernel(String name, PeekMode peekMode, boolean readerScratch, Scheduler scheduler) {
    super(Policy.DOTC, scheduler); this.name = name; this.peekMode = peekMode; this.readerScratch = readerScratch;
  }

  public String name() { return name; }
  public long work() { return counters.total(); }

  public void reload(List<Ast.Source> ss) {
    for (Ast.Source s : ss) sources.put(s.name(), s);
    newRun(new ArrayList<>(sources.values()));              // one run, one symbol table, for every file
  }

  // ---- readers and the scheduler ----------------------------------------------------------------------

  public enum State { RUNNABLE, WAITING, DONE }

  /** A request on its own thread. */
  public final class Reader {
    public final String id; public final Ask ask;
    final Semaphore go = new Semaphore(0);
    public volatile State state = State.RUNNABLE;
    public volatile Object waitingOn;
    String savedTarget;
    public String answer;
    public int safepoints = 0;
    public final List<String> trace = new ArrayList<>();
    Thread thread;
    Reader(String id, Ask ask) { this.id = id; this.ask = ask; }
    @Override public String toString() { return id; }
  }

  /** What the harness drives: the holes (a symbol's completer, a declaration's typing) and their owners, the
   * readers, and the handshake that lets exactly one reader run between two of its safepoints. */
  public final class Sched {
    final Semaphore back = new Semaphore(0);
    final Map<Object, Reader> holes = new HashMap<>();
    public final List<Reader> readers = new ArrayList<>();
    public volatile Reader current;
    public boolean deadlock = false;

    public Reader reader(String id, Ask ask) { Reader r = new Reader(id, ask); readers.add(r); return r; }

    /** Start the reader's thread; it runs only when given a turn. */
    public void start(Reader r) {
      r.thread = new Thread(() -> {
        r.go.acquireUninterruptibly();
        current = r; if (readerScratch) targetPath = r.savedTarget;
        try { r.answer = serve(r.ask); }
        catch (Cancelled c) { r.answer = "<cancelled>"; }
        catch (RuntimeException e) { r.answer = "<failed: " + e + ">"; }
        finally { r.state = State.DONE; unwindAll(r); back.release(); }
      }, "reader-" + r.id);
      r.thread.setDaemon(true);
      r.thread.start();
    }

    /** Run `r` until its next safepoint, its wait, or its end. */
    public void turn(Reader r) {
      if (r.state != State.RUNNABLE) throw new IllegalStateException(r + " is " + r.state);
      current = r;
      r.go.release();
      back.acquireUninterruptibly();
    }

    /** Called on the reader's thread: give the turn back and wait for the next one. */
    private void pause(Reader r) {
      if (readerScratch) r.savedTarget = targetPath;
      back.release();
      r.go.acquireUninterruptibly();
      current = r;
      if (readerScratch) targetPath = r.savedTarget;
      if (deadlock) throw new Cancelled("deadlock");
    }

    void safepoint(String where) {
      Reader r = current;
      if (r == null) return;                                  // the harness's own typing after the readers
      r.safepoints++; r.trace.add(where);
      pause(r);
    }

    /** Wait on the barrier of `key`, held by another reader, unless that would close a wait-for cycle. */
    void waitOn(Object key, String what) {
      Reader r = current, owner = holes.get(key);
      if (owner != null && owner.state == State.WAITING && holes.get(owner.waitingOn) == r)
        throw new CyclicReference(what);                      // §4.2: the wait would close a cycle
      r.state = State.WAITING; r.waitingOn = key;
      r.trace.add("wait " + what);
      pause(r);
    }

    void take(Object key) { holes.put(key, current); }

    void release(Object key) {
      holes.remove(key);
      for (Reader w : readers) if (w.state == State.WAITING && key.equals(w.waitingOn)) { w.state = State.RUNNABLE; w.waitingOn = null; }
    }

    /** A reader that ends (its answer given, or an unwinding that escaped) holds nothing. */
    void unwindAll(Reader r) {
      for (Object k : new ArrayList<>(holes.keySet())) if (holes.get(k) == r) { release(k); if (k instanceof Sym s) { s.locked = false; } }
    }

    public boolean allDone() { for (Reader r : readers) if (r.state != State.DONE) return false; return true; }
    public Reader owner(Object key) { return holes.get(key); }
  }

  public final Sched sched = new Sched();

  @Override protected void signalDone(Unit unit, String where, Target reached) { sched.safepoint(where); }
  @Override protected void onEvent(Event e) {}
  @Override protected void checkForMoreWork(String where) {}

  // ---- completion as lazy resolve ---------------------------------------------------------------------

  /** `Symbol.info` with an owner on the black hole (§3.1). */
  @Override public Object force(Sym s) {
    while (true) {
      if (!(s.info instanceof Completer c)) return s.info;
      Reader owner = sched.owner(s);
      if (owner == null) {
        s.locked = true; sched.take(s); lockedCount++; counters.completers++;
        boolean ok = false;
        try {
          Object r = c.complete(s);
          s.info = r; ok = true;                              // published, consistent, once
          return r;
        } finally {
          lockedCount--;
          s.locked = false; sched.release(s);                 // an unwound completion leaves the symbol completable
        }
      }
      if (owner == sched.current) throw new CyclicReference(s.name);   // a re-entry on this reader: the cycle of today
      sched.waitOn(s, s.name);                                // the other reader's: wait, then look again
    }
  }

  /** The toy's `isCompleting`: is the member of a view being completed, by whoever the mode says. */
  private boolean isCompleting(Sym m) {
    Reader owner = sched.owner(m);
    return owner != null && (peekMode == PeekMode.ANY || owner == sched.current);
  }

  /** scalac's implicit search skipping a candidate whose info is `LOCKED` (`isCyclicOrErroneous`): here the view's
   * member is skipped while it is being completed. */
  @Override public Sym findImplicit(Unit u, Type t, String name) {
    for (Sym cand : toplevel.syms()) {
      if (cand.factoryOf == null) continue;
      if (t.cls() == null || !t.cls().name.equals(cand.paramType)) continue;
      Sym m = lookupMember(cand.factoryOf, name);
      if (m == null) continue;
      if (isCompleting(m)) { sched.current.trace.add("peek " + m.owner.name + "." + m.name + " completing"); continue; }
      return cand;
    }
    return null;
  }

  /** The path session's targeting (`dotc-session-path`, every fix on). */
  @Override protected boolean targetsList(String owner, boolean inline) {
    if (targetPath == null || inline) return false;
    return contains(owner, targetPath);
  }

  // ---- a request --------------------------------------------------------------------------------------

  /** A declaration's typing as a fact with a barrier (§3.2): typed, being typed by a reader, or not typed. */
  private String declKey(Unit u, int i) { return "decl " + u.name() + "#" + i; }

  private void typeDeclAwaiting(Unit u, int i) {
    while (!u.typedDecls.get(i)) {
      Reader owner = sched.owner(declKey(u, i));
      if (owner == null) {
        sched.take(declKey(u, i));
        try { typeDecls(u, List.of(i)); }
        finally { sched.release(declKey(u, i)); }
        return;
      }
      if (owner == sched.current) return;                     // our own (a resume into it)
      sched.waitOn(declKey(u, i), "decl " + u.source.decls().get(i).name());
    }
  }

  private String serve(Ask ask) {
    if (!sources.containsKey(ask.file())) return "<no such file>";
    Unit u = units.get(ask.file());
    switch (ask) {
      case Ask.Completion c -> {
        Ast.Source s = sources.get(c.file());
        int idx = 0;
        for (int i = 0; i < s.decls().size(); i++) if (s.decls().get(i).name().equals(c.decl())) idx = i;
        targetPath = c.decl() + "." + c.member();
        try {
          typeDeclAwaiting(u, idx);
          resumeSkipped(u, targetPath);
        } finally { targetPath = null; }
        return completionAnswer(u, new Target(c.decl(), c.member()));
      }
      case Ask.LoadedTyped l -> { finish(u); return unitAnswer(u); }
    }
  }

  /** The rest of the unit, typed by whoever asks for the whole of it (the harness, after the readers). */
  public void finish(Unit u) {
    List<Integer> all = new ArrayList<>();
    for (int i = 0; i < u.source.decls().size(); i++) all.add(i);
    for (int i : all) typeDeclAwaiting(u, i);
    if (!u.typed) typeDecls(u, all);
  }

  public Collection<Unit> allUnits() { return units.values(); }
}
