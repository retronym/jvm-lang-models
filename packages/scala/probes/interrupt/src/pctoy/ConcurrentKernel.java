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
 * the other reader is waited for like any other fact.
 *
 * Roots (§3.1 "Groups", `CompletionRoots` in the implementation): what a completion claims, and what another
 * reader waits on, is a root, which may be coarser than the symbol. `RootMode.FACT` is the Namer's: the root is
 * the symbol. `PAIR` is the symbol loader's: a class, its companion and every member of either are one root (the
 * loader completes the class and the module from one classfile), so a completion of any of them claims the pair.
 * `FILE` is TASTy's: every symbol of one source file is one root (one `TreeUnpickler` and its address maps serve
 * the file). The claim is reentrant for its owner; the black hole stays per symbol, so a re-entry on the owner is
 * still the cycle of today (`Touched`, `InProgress`). A coarser root turns a lock order into a wait-for cycle that
 * is no dependency cycle (lesson 6 of §11): two readers that take two roots in opposite orders close a cycle the
 * sequential run never sees, and `CyclicReference` there is a false error (I54).
 *
 * `CycleRule` is what the reader that closes a wait-for cycle does. `RAISE` is §4.2 as first written: it throws
 * `CyclicReference`. `VICTIM` is the implementation's deviation (§8 step 4, I74): a reader typing a body is the
 * victim, it unwinds everything it holds and its request is retried from scratch, at most `MAX_RETRIES` times
 * before the answer is a livelock; a reader inside a Namer completion is never aborted, because an unwound Namer
 * completion cannot run again (I53): it waits, and the other party is aborted if it can be; when both are inside
 * Namer completions, the reader with the lower id raises, the single-reader answer (I54, I87). The depth that
 * decides "inside a Namer completion" counts completions under `FACT` roots only: a loader's or a TASTy completion
 * (`PAIR`, `FILE`) can run again, so a reader inside one is a body-typing reader for the rule.
 *
 * A root may carry shared scratch beyond its facts' black holes: TASTy's `treeAtAddr` holds a `PoisonTree` at a
 * definition's address while it is read (`TreeUnpickler.readIndexedDef`). The toy's `reading` set per `FILE` root
 * is that sentinel, set when a completion starts and cleared when it publishes; with `scratchFinally` false, as
 * `readIndexedDef` has it (no try/finally), an owner that unwinds leaves it, and the reader that takes the root
 * over meets it and fails with "cyclic reference while unpickling", an `UnpicklingError` the typer does not catch as a
 * cycle, so the request that meets it fails: a false cycle (I87's second source). With `scratchFinally` true the
 * unwinding owner clears it. */
public final class ConcurrentKernel extends Global {
  public enum PeekMode { OWN, ANY }
  public enum RootMode { FACT, PAIR, FILE }
  public enum CycleRule { RAISE, VICTIM }
  public static final int MAX_RETRIES = 5;

  private final String name;
  private final PeekMode peekMode;
  /** Save and restore the per-request scratch at a switch; off, the two readers share `targetPath` (kind A). */
  private final boolean readerScratch;
  private final RootMode rootMode;
  private final CycleRule cycleRule;
  /** Clear a `FILE` root's reading sentinel on an unwind too (true) or only on publication (false, dotc). */
  private final boolean scratchFinally;
  private final Map<String, Ast.Source> sources = new LinkedHashMap<>();

  public ConcurrentKernel(String name, PeekMode peekMode, boolean readerScratch, Scheduler scheduler) {
    this(name, peekMode, readerScratch, RootMode.FACT, CycleRule.RAISE, true, scheduler);
  }

  public ConcurrentKernel(String name, PeekMode peekMode, boolean readerScratch, RootMode rootMode, CycleRule cycleRule,
                          boolean scratchFinally, Scheduler scheduler) {
    super(Policy.DOTC, scheduler); this.name = name; this.peekMode = peekMode; this.readerScratch = readerScratch;
    this.rootMode = rootMode; this.cycleRule = cycleRule; this.scratchFinally = scratchFinally;
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
    public volatile Object waitingOn; String waitingWhat;
    String savedTarget;
    public String answer;
    public int safepoints = 0;
    /** The harness cancels this reader at its `cancelAt`th safepoint (0: never): the abort of §3.1 with a waiter. */
    public int cancelAt = 0;
    /** Namer completions in progress on this reader (dotc's `namerCompletionDepth`): a reader at depth 0 can be aborted. */
    int namerDepth = 0;
    /** Set on a waiting reader by the one that closes a cycle: abort, or raise the cycle, when it resumes. */
    boolean abortPending; String raisePending;
    public int aborts = 0; public boolean livelock = false;
    public final List<String> trace = new ArrayList<>();
    Thread thread;
    Reader(String id, Ask ask) { this.id = id; this.ask = ask; }
    @Override public String toString() { return id; }
  }

  /** A root's or a declaration's claim: its owner and how many times the owner holds it. */
  static final class Claim { final Reader owner; int depth = 1; Claim(Reader owner) { this.owner = owner; } }

  /** What the harness drives: the black holes (a symbol's completer) and their owners, the claims (a root, a
   * declaration's typing) that are waited on, the readers, and the handshake that lets exactly one reader run
   * between two of its safepoints. */
  public final class Sched {
    final Semaphore back = new Semaphore(0);
    final Map<Sym, Reader> holes = new HashMap<>();
    final Map<Object, Claim> claims = new HashMap<>();
    /** Per `FILE` root, the definitions being read: TASTy's `PoisonTree` entries of `treeAtAddr`. */
    final Map<Object, Set<Sym>> reading = new HashMap<>();
    public final List<Reader> readers = new ArrayList<>();
    public volatile Reader current;
    public boolean deadlock = false;

    public Reader reader(String id, Ask ask) { Reader r = new Reader(id, ask); readers.add(r); return r; }

    /** Start the reader's thread; it runs only when given a turn. A victim's request is retried from scratch, after
     * giving the turn back once (the driver re-queues it), until it answers or the retry bound is hit. */
    public void start(Reader r) {
      r.thread = new Thread(() -> {
        r.go.acquireUninterruptibly();
        current = r; if (readerScratch) targetPath = r.savedTarget;
        try {
          boolean retry = false;
          while (true) {
            try { if (retry) pause(r); r.answer = serve(r.ask); break; }
            catch (Victim v) {
              r.aborts++; unwindAll(r); targetPath = null;
              r.trace.add("abort " + v.getMessage());
              if (r.aborts >= MAX_RETRIES) { r.livelock = true; r.answer = "<livelock: aborted " + r.aborts + " times>"; break; }
              r.trace.add("retry"); retry = true;
            }
          }
        }
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
      if (r.abortPending) { r.abortPending = false; throw new Victim("wound by the other reader"); }
      if (r.raisePending != null) { String what = r.raisePending; r.raisePending = null; throw new CyclicReference(what); }
    }

    void safepoint(String where) {
      Reader r = current;
      if (r == null) return;                                  // the harness's own typing after the readers
      r.safepoints++; r.trace.add(where);
      if (r.safepoints == r.cancelAt) { r.trace.add("cancelled"); throw new Cancelled("cancelled at " + where); }
      pause(r);
    }

    /** The reader that `r` would wait for, if waiting on `key`'s owner closes a wait-for cycle back to `r`; null if
     * not. Each reader waits on at most one claim, so following owners is the whole check (10.7's `wouldDeadlock`). */
    private Reader closesCycle(Reader r, Object key) {
      Reader o = claims.get(key).owner;
      for (Reader w = o; w != null; ) {
        if (w.state != State.WAITING || w.waitingOn == null) return null;
        Claim c = claims.get(w.waitingOn);
        if (c == null) return null;
        if (c.owner == r) return o;
        w = c.owner;
      }
      return null;
    }

    /** Wait on the claim of `key`, held by another reader, unless that would close a wait-for cycle, which the
     * kernel's `CycleRule` settles. */
    void waitOn(Object key, String what) {
      Reader r = current, o = closesCycle(r, key);
      if (o != null) {
        switch (cycleRule) {
          case RAISE -> throw new CyclicReference(what);        // §4.2: the wait would close a cycle
          case VICTIM -> {
            if (r.namerDepth == 0) throw new Victim("victim at " + what);      // typing a body: abort and retry
            if (o.namerDepth == 0) { o.abortPending = true; wake(o); }         // the other party can be aborted: it is
            else if (r.id.compareTo(o.id) < 0) throw new CyclicReference(what); // both in Namer completions: by id
            else { o.raisePending = o.waitingWhat; wake(o); }
          }
        }
      }
      r.state = State.WAITING; r.waitingOn = key; r.waitingWhat = what;
      r.trace.add("wait " + what);
      pause(r);
    }

    private void wake(Reader w) { w.state = State.RUNNABLE; w.waitingOn = null; }

    /** Claim `key` for the current reader, or hold it once more. */
    void acquire(Object key) {
      Claim c = claims.get(key);
      if (c == null) claims.put(key, new Claim(current)); else c.depth++;
    }

    /** Give `key` up once; the last release wakes its waiters. */
    void release(Object key) {
      Claim c = claims.get(key);
      if (c != null && --c.depth > 0) return;
      claims.remove(key);
      for (Reader w : readers) if (w.state == State.WAITING && key.equals(w.waitingOn)) wake(w);
    }

    /** A reader that ends, or is retried, holds nothing. The reading sentinels stay: they are the root's scratch,
     * not the reader's. */
    void unwindAll(Reader r) {
      for (Object k : new ArrayList<>(claims.keySet())) if (claims.get(k).owner == r) { claims.remove(k); for (Reader w : readers) if (w.state == State.WAITING && k.equals(w.waitingOn)) wake(w); }
      for (Sym s : new ArrayList<>(holes.keySet())) if (holes.get(s) == r) { holes.remove(s); s.locked = false; }
    }

    public boolean allDone() { for (Reader r : readers) if (r.state != State.DONE) return false; return true; }
    public Reader owner(Object key) { Claim c = claims.get(key); return c == null ? null : c.owner; }
  }

  /** The abort of a reader chosen as a wait-for cycle's victim (dotc: a `CancelledCompilation` the driver retries). */
  static final class Victim extends RuntimeException {
    Victim(String why) { super(why, null, false, false); }
  }

  public final Sched sched = new Sched();

  @Override protected void signalDone(Unit unit, String where, Target reached) { sched.safepoint(where); }
  @Override protected void onEvent(Event e) {}
  @Override protected void checkForMoreWork(String where) {}

  // ---- completion as lazy resolve ---------------------------------------------------------------------

  /** The root a completion of `s` claims: the symbol, its top-level declaration's pair, or its file. */
  private Object rootOf(Sym s) {
    switch (rootMode) {
      case FACT: return s;
      case PAIR: { Sym top = s; while (top.owner != null) top = top.owner; return "pair " + top.name; }
      default: return "file " + s.file;
    }
  }

  /** `Symbol.info` with an owner on the black hole (§3.1) and the wait on the root. */
  @Override public Object force(Sym s) {
    while (true) {
      if (!(s.info instanceof Completer c)) return s.info;
      Reader me = sched.current;
      Reader h = sched.holes.get(s);
      if (h != null && h == me) throw new CyclicReference(s.name);   // a re-entry on this reader: the cycle of today
      Object root = rootOf(s);
      Reader owner = sched.owner(root);
      if (owner != null && owner != me) { sched.waitOn(root, s.name); continue; }   // the other reader's: wait, then look again
      sched.acquire(root); sched.holes.put(s, me);
      s.locked = true; lockedCount++; counters.completers++;
      if (me != null && rootMode == RootMode.FACT) me.namerDepth++;   // me is null for the harness's own typing after the readers
      Set<Sym> reading = rootMode == RootMode.FILE ? sched.reading.computeIfAbsent(root, k -> new HashSet<>()) : null;
      try {
        if (reading != null && !reading.add(s)) throw new UnpicklingError(s.name);
        Object r = c.complete(s);
        s.info = r;                                           // published, consistent, once
        if (reading != null) reading.remove(s);               // `readIndexedDef`: cleared on the way out, not in a finally
        return r;
      } finally {
        if (reading != null && scratchFinally) reading.remove(s);
        if (me != null && rootMode == RootMode.FACT) me.namerDepth--;
        lockedCount--;
        s.locked = false; sched.holes.remove(s); sched.release(root);   // an unwound completion leaves the symbol completable
      }
    }
  }

  /** The toy's `isCompleting`: is the member of a view being completed, by whoever the mode says. */
  private boolean isCompleting(Sym m) {
    Reader owner = sched.holes.get(m);
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
        sched.acquire(declKey(u, i));
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
