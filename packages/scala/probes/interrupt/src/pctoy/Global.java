package pctoy;

import java.util.*;
import java.util.function.Supplier;
import pctoy.Core.*;

/** A symbol table of lazy facts with runs, as scalac and dotc have it: symbols whose infos are completers
 * until forced, a `LOCKED`/`Touched` flag as the black hole, a per-run namer that enters a unit's
 * definitions, and a typer that forces the facts in declaration order and calls `signalDone` at every
 * point where a presentation compiler could observe the state. The kernels subclass it and decide what
 * happens at those points. `Policy` holds the choices scala/scala#11328 changed and the one scalac and
 * dotc make differently. */
public abstract class Global {
  public enum Kind { CLASS, OBJECT, TRAIT, DEF }

  public static final class Sym {
    public final String name; public final Kind kind; public final String file; public final int id;
    public Ast.Decl decl; public Ast.Member member; public Sym owner;
    public Set<String> mods = Set.of();
    public boolean synthetic; public Sym factoryOf; public String paramType;
    public Object info;            // Completer | ClassInfo | Type
    public boolean locked, unlinked;
    public int defRunId;
    /** scalac's `SynthesizedMethods` attachment: synthetic trees added by a targeted check, kept for the full one. */
    public List<String> synthesized; public int synthesizedRun = -1;
    /** Members another declaration's desugaring merged into this one (a case class's `apply`/`unapply` into its
     * companion, `copy` into itself): dotc merges them into the tree, so a fresh symbol for the tree lacks them. */
    public List<Sym> merged = new ArrayList<>();
    /** A local's or an anonymous class member's name path (`M.m.a`, `M.sel.foo`) and the context it is typed in;
     * null for a declaration's member, whose path is `owner.name` and whose context is its class. */
    public String path; public Ctx ctx;
    /** A block or anonymous-class body's typed tree, once typed: dotc's `TypedAhead` when the member's completer typed
     * it (an inferred result type), reused as is when the member itself is typed. */
    public TypedBody typedBody;
    Sym(String name, Kind kind, String file, int id) { this.name = name; this.kind = kind; this.file = file; this.id = id; }
    public boolean isTerm() { return kind == Kind.OBJECT || kind == Kind.DEF; }
    @Override public String toString() { return name + "#" + id; }
  }

  public record Type(Sym cls, String builtin, String error) {
    public static Type of(Sym c) { return new Type(c, null, null); }
    public static Type builtin(String n) { return new Type(null, n, null); }
    public static Type err(String m) { return new Type(null, null, m); }
    public boolean isError() { return error != null; }
    public String show() { return cls != null ? cls.name : builtin != null ? builtin : "<error: " + error + ">"; }
  }

  public static final class ClassInfo { public Sym parent; public final Scope decls = new Scope(); }

  /** Two namespaces, as in Scala: types (classes, traits) and terms (objects, defs). */
  public static final class Scope {
    private final LinkedHashMap<String, Sym> types = new LinkedHashMap<>(), terms = new LinkedHashMap<>();
    private LinkedHashMap<String, Sym> ns(Sym s) { return s.isTerm() ? terms : types; }
    public void enter(Sym s) { ns(s).put(s.name, s); }
    public void unlink(Sym s) { if (ns(s).get(s.name) == s) ns(s).remove(s.name); s.unlinked = true; }
    public Sym term(String n) { return terms.get(n); }
    public Sym type(String n) { return types.get(n); }
    public List<Sym> syms() { List<Sym> r = new ArrayList<>(types.values()); r.addAll(terms.values()); return r; }
  }

  public interface Completer { Object complete(Sym s); }

  /** Where a body's names are looked up: a block's locals (those entered before the statement), else the class's
   * members, else the enclosing context; then the top-level terms. `inline` when inside an inline method's body. */
  public record Ctx(Sym cls, Map<String, Sym> locals, Ctx outer, boolean inline) {}

  /** The typed tree of a block or of an anonymous class's template: per statement its symbol and typed type, or a
   * stub (type null: a statement skipped by targeting, its symbol entered but its tree untyped; for a template, a
   * member not entered at all). `display` is what the unit's answer prints, kept current when a stub is resumed. */
  public static final class TypedBody {
    public final List<String> names = new ArrayList<>();
    public final List<Sym> syms = new ArrayList<>();
    public final List<Type> types = new ArrayList<>();
    public final List<String> display = new ArrayList<>();
    public Type result; public boolean complete;
    int add(Sym s) { names.add(s.name); syms.add(s); types.add(null); display.add("<stub " + s.name + ">"); return names.size() - 1; }
    void set(int i, Type t) { types.set(i, t); display.set(i, names.get(i)); }
    public List<String> stubs() { List<String> r = new ArrayList<>(); for (int i = 0; i < names.size(); i++) if (types.get(i) == null) r.add(names.get(i)); return r; }
  }

  /** A statement of a nested list skipped on the request's path, kept with what types and splices it later: the
   * spike's `SkippedStat` for a block's statement. Off the path a skipped statement is not recorded: the list it
   * belongs to was typed by a completer, and its typed tree is a cached value, not part of the unit's tree yet. */
  public record Skipped(String path, Runnable resume) {}

  public record Target(String decl, String member) {}

  public static final class Unit {
    public Ast.Source source;
    public final Map<Sym, Integer> synthetics = new LinkedHashMap<>();  // synthetic tree → the declaration it came from
    public final List<Problem> problems = new ArrayList<>(), suspended = new ArrayList<>();
    public final Set<String> suppressions = new HashSet<>();
    public boolean suppressionsKnown;
    public Map<String, List<String>> bodies = new LinkedHashMap<>();
    public boolean typed;
    /** A session's typed set: the declarations typed so far by targeted runs, by index (dotc spike: the typed
     * statements of `Session`; the others are its `SkippedStat`s). */
    public final BitSet typedDecls = new BitSet();
    /** The run the session's targeted typing belongs to, or -1: a later run cannot resume it. */
    public int sessionRun = -1;
    /** The declaration being typed by `typeDecls`, or -1. */
    public int typing = -1;
    public Target target;
    public List<Sym> implicitCache; public int implicitCacheRun = -1;
    /** The nested statements skipped on a request's path, resumed when a later request lands in one or the unit is finished. */
    public final List<Skipped> skipped = new ArrayList<>();
    public String name() { return source.name(); }
    void reset(Ast.Source s) {
      source = s; synthetics.clear(); skipped.clear(); problems.clear(); suspended.clear(); suppressions.clear();
      suppressionsKnown = false; bodies = new LinkedHashMap<>(); typed = false; typedDecls.clear(); sessionRun = -1; typing = -1; target = null; implicitCache = null;
    }
  }

  /** The choices under test. The first four are what scala/scala#11328 changed (false = before, true = after);
   * `unlockOnUnwind` is scalac (true, `completeInfo`'s `finally unlock()`) against dotc (false, `Touched` stays);
   * `reuseSymbols` is scalac's `enterExistingSym` (true) against dotc's `unlinkFromFile` and fresh symbols (false). */
  public record Policy(boolean uninterruptibleSynthesis, boolean keepSyntheticsForTargeted, boolean keepFactory,
                       boolean suspendTargetedWarnings, boolean unlockOnUnwind, boolean reuseSymbols) {
    public static final Policy SCALAC_BEFORE = new Policy(false, false, false, false, true, true);
    public static final Policy SCALAC_AFTER = new Policy(true, true, true, true, true, true);
    public static final Policy DOTC = new Policy(true, true, true, true, false, false);
  }

  public final Policy policy;
  public final Scope toplevel = new Scope();
  public final Map<String, Unit> units = new LinkedHashMap<>();
  public int runId = 0, lockedCount = 0, nextId = 0;
  public boolean interruptsEnabled = true;
  public final Counters counters = new Counters();
  public final Scheduler scheduler;
  /** The request's target as a name path (`Use.u`, `M.m.b`) while a targeted typer runs, else null: what decides, per
   * nested statement list, whether it is targeted (`targetsList`). */
  protected String targetPath;

  protected Global(Policy policy, Scheduler scheduler) { this.policy = policy; this.scheduler = scheduler; }

  // ---- hooks for the kernels --------------------------------------------------------------------------

  /** Called at every safepoint. `reached` is the target a targeted check has just typed, if any. */
  protected void signalDone(Unit unit, String where, Target reached) {
    Event ev = scheduler.at(where);
    if (ev != null) onEvent(ev);
    if (!interruptsEnabled || lockedCount > 0) return;
    if (reached != null && reaches(reached, unit.target)) throw new TyperResult(completionAnswer(unit, unit.target));
    checkForMoreWork(where);
  }
  /** A member typed whole reaches a target inside its body too. */
  private static boolean reaches(Target reached, Target target) {
    return target != null && (reached.equals(target) || reached.decl().equals(target.decl()) && target.member().startsWith(reached.member() + "."));
  }
  /** Whether a nested statement list (a block's locals, an anonymous template's members) owned by the tree at `owner`
   * is targeted: its statements off the path to `targetPath` skipped. Default: typed whole. */
  protected boolean targetsList(String owner, boolean inline) { return false; }
  /** `owner` is on the path to `target`: the target is the tree at `owner` or inside it. */
  protected static boolean contains(String owner, String target) { return target != null && (target.equals(owner) || target.startsWith(owner + ".")); }
  /** A problem of the unit (the revisions kernel keeps it with the fact being computed). */
  protected void report(Unit u, Problem p) { u.problems.add(p); }
  /** The harness injected an event at this safepoint. */
  protected abstract void onEvent(Event e);
  /** A safepoint where requests may be serviced (scalac: `pollForWork`). */
  protected abstract void checkForMoreWork(String where);

  public final <T> T uninterruptible(Supplier<T> op) {
    boolean saved = interruptsEnabled;
    interruptsEnabled = false;
    try { return op.get(); } finally { interruptsEnabled = saved; }
  }

  // ---- runs and the namer -----------------------------------------------------------------------------

  /** A new run over these sources: symbols of a reloaded file are reused (scalac) or replaced (dotc), and
   * their infos become completers again. */
  public void newRun(List<Ast.Source> sources) {
    runId++;
    for (Ast.Source s : sources) {
      Unit u = units.computeIfAbsent(s.name(), k -> new Unit());
      u.reset(s);
      if (!policy.reuseSymbols) unlinkFromFile(s.name());
      for (Ast.Decl d : s.decls()) enterDecl(u, d);
      for (Ast.Decl d : s.decls()) if (d.isCase() && !d.isObject()) ensureCompanion(u, d);
    }
  }

  /** dotc's `unlinkFromFile`: the file's symbols from earlier runs leave the scope; references from other
   * files' facts to them are stale, and resolve by name again (`bringForward` in `Mode.Interactive`). */
  private void unlinkFromFile(String file) {
    for (Sym s : toplevel.syms()) if (s.file.equals(file) && s.defRunId != runId) toplevel.unlink(s);
  }

  Sym newSym(String name, Kind kind, String file) { return new Sym(name, kind, file, nextId++); }

  private static Kind kindOf(Ast.Decl d) {
    return switch (d.kind()) { case "object" -> Kind.OBJECT; case "trait" -> Kind.TRAIT; default -> Kind.CLASS; };
  }

  void enterDecl(Unit u, Ast.Decl d) {
    Kind kind = kindOf(d);
    Sym existing = kind == Kind.OBJECT ? toplevel.term(d.name()) : toplevel.type(d.name());
    Sym sym;
    if (existing != null && existing.file.equals(u.name()) && existing.kind == kind && policy.reuseSymbols) {
      sym = existing;                                   // scalac: enterExistingSym keeps the symbol
    } else {
      if (existing != null && existing.file.equals(u.name())) toplevel.unlink(existing);
      sym = newSym(d.name(), kind, u.name());
      toplevel.enter(sym);
    }
    sym.decl = d; sym.mods = d.mods(); sym.synthetic = false; sym.defRunId = runId; sym.locked = false;
    sym.info = classCompleter(u, sym);
    sym.synthesized = null; sym.merged = new ArrayList<>();
    if (d.isImplicit()) enterImplicitWrapper(u, sym, d);   // the namer enters the factory (enterClassDef)
  }

  /** A case class without an `object` of its own gets a synthetic companion; both get `apply` and `unapply`
   * whose trees wait in `unit.synthetics` until the typer adds them to the companion's body. */
  void ensureCompanion(Unit u, Ast.Decl d) {
    Sym cls = toplevel.type(d.name());
    Sym companion = toplevel.term(d.name());
    if (companion == null || !companion.file.equals(u.name()) || companion.kind != Kind.OBJECT) {
      companion = newSym(d.name(), Kind.OBJECT, u.name());
      companion.synthetic = true; companion.defRunId = runId;
      companion.decl = new Ast.Decl(Set.of(), "object", d.name(), List.of(), null, List.of(), d.pos());
      companion.info = classCompleter(u, companion);
      toplevel.enter(companion);
      u.synthetics.put(companion, d.pos());
    }
    companion.merged.removeIf(s -> s.name.equals("apply") || s.name.equals("unapply"));
    cls.merged.removeIf(s -> s.name.equals("copy"));
    for (String m : List.of("apply", "unapply")) {
      Sym s = newSym(m, Kind.DEF, u.name());
      s.owner = companion; s.synthetic = true; s.defRunId = runId;
      s.info = (Completer) self -> Type.of(cls);
      u.synthetics.put(s, d.pos());
      companion.merged.add(s);
    }
    Sym copy = newSym("copy", Kind.DEF, u.name());              // Namers.addCopyMethod: the namer's synthetic
    copy.owner = cls; copy.synthetic = true; copy.defRunId = runId;
    copy.info = (Completer) self -> Type.of(cls);
    u.synthetics.put(copy, d.pos());
    cls.merged.add(copy);
  }

  /** scalac's `enterImplicitWrapper`, run each time the enclosing template is typed: the factory method of
   * an implicit class. Before the fix a new symbol replaced the old one; after it, the symbol is kept and
   * only its tree renewed. */
  private void enterImplicitWrapper(Unit u, Sym cls, Ast.Decl d) {
    Sym existing = toplevel.term(d.name());
    boolean isFactory = existing != null && existing.factoryOf != null && existing.file.equals(u.name());
    Sym factory;
    if (isFactory && policy.keepFactory) {
      factory = existing;
    } else {
      if (isFactory) toplevel.unlink(existing);
      factory = newSym(d.name(), Kind.DEF, u.name());
      factory.synthetic = true;
      toplevel.enter(factory);
    }
    factory.factoryOf = cls; factory.defRunId = runId;
    factory.paramType = d.params().isEmpty() ? null : d.params().get(0).tpe();
    factory.info = (Completer) self -> Type.of(cls);
    u.synthetics.put(factory, d.pos());
  }

  // ---- forcing ----------------------------------------------------------------------------------------

  /** `Symbol.info`: run the completer once, with the black hole set; scalac resets it however the completer
   * ends, dotc only when it returns. On a cycle scalac gives the symbol `ErrorType`, dotc leaves it lazy. */
  public Object force(Sym s) {
    if (!(s.info instanceof Completer c)) return s.info;
    if (s.defRunId != runId && refusesAcrossRuns()) {   // dotc's Namer.Completer in a later run: UnspecifiedErrorType
      s.info = s.kind == Kind.DEF ? Type.err("unspecified") : new ClassInfo();
      return s.info;
    }
    if (s.locked) {
      if (policy.unlockOnUnwind) s.info = Type.err("cyclic reference involving " + s.name);
      throw new CyclicReference(s.name);
    }
    s.locked = true; lockedCount++; counters.completers++;
    boolean ok = false;
    try {
      Object r = c.complete(s);
      s.info = r; ok = true;
      return r;
    } finally {
      lockedCount--;
      if (ok || policy.unlockOnUnwind) s.locked = false;
    }
  }

  /** dotc: a Namer completer refuses to run in a run later than the one that indexed it (finding I7), and the
   * symbol gets `UnspecifiedErrorType` (a class: no members). scalac re-enters instead. */
  protected boolean refusesAcrossRuns() { return false; }

  public ClassInfo classInfo(Sym cls) { return (ClassInfo) force(cls); }

  /** A stale symbol (dotc: unlinked by a later run of its file) resolves by name to the current one. */
  public Sym current(Sym s) {
    if (!s.unlinked) return s;
    Sym now = s.isTerm() ? toplevel.term(s.name) : toplevel.type(s.name);
    return now != null ? now : s;
  }

  private Completer classCompleter(Unit u, Sym cls) {
    return self -> {
      Ast.Decl d = cls.decl;
      ClassInfo ci = new ClassInfo();
      if (d.parent() != null) {
        Sym p = toplevel.type(d.parent());
        if (p == null) u.problems.add(new Problem("error", u.name(), d.name(), "not found: type " + d.parent()));
        else ci.parent = p;
      }
      if (d.isCase()) for (Ast.Param p : d.params()) {
        Sym m = newSym(p.name(), Kind.DEF, u.name());
        m.owner = cls; m.defRunId = runId; m.member = new Ast.Member(Set.of(), p.name(), p.tpe(), null, -1);
        m.info = memberCompleter(u, m);
        ci.decls.enter(m);
      }
      for (Ast.Member mem : d.members()) {
        Sym m = newSym(mem.name(), Kind.DEF, u.name());
        m.owner = cls; m.defRunId = runId; m.member = mem; m.mods = mem.mods();
        m.info = memberCompleter(u, m);
        ci.decls.enter(m);
      }
      for (Sym s : cls.merged) ci.decls.enter(s);
      return ci;
    };
  }

  private Completer memberCompleter(Unit u, Sym m) {
    return self -> {
      Ast.Member mem = m.member;
      String where = pathOf(m);
      Type t;
      if (!mem.inferred()) {
        Sym c = toplevel.type(mem.declared());
        t = c != null ? Type.of(c) : Type.err("not found: type " + mem.declared());
      } else if (mem.body() != null) {
        t = typedBodyOf(u, m).result;                         // typed ahead (`typedAheadExpr`), under whatever target is set
      } else {
        try { t = typePath(u, ctxOf(m), mem.path(), where); }
        catch (CyclicReference e) { t = Type.err(e.getMessage()); }
      }
      if (t.isError()) report(u, new Problem("error", u.name(), where, t.error()));
      signalDone(u, "rhs " + where, null);
      return t;
    };
  }

  public static String pathOf(Sym m) { return m.path != null ? m.path : m.owner.name + "." + m.name; }
  protected static Ctx ctxOf(Sym m) { return m.ctx != null ? m.ctx : new Ctx(m.owner, null, null, false); }

  /** The typed body of a member with a block or an anonymous class: the cached one if complete (dotc's `TypedAhead`,
   * reused whatever target it was typed under), else typed now. */
  protected TypedBody typedBodyOf(Unit u, Sym m) {
    if (m.typedBody != null && m.typedBody.complete) return m.typedBody;
    return typeBody(u, m);
  }

  /** Types a block or an anonymous template under the current `targetPath`: a targeted list skips the statements off
   * the path, leaving stubs; those on the path are recorded on the unit for resumption. */
  protected TypedBody typeBody(Unit u, Sym m) {
    Ctx outer = ctxOf(m);
    boolean inline = outer.inline() || m.mods.contains("inline");
    String path = pathOf(m);
    TypedBody tb = new TypedBody();
    m.typedBody = tb;
    boolean targeted = targetsList(path, inline), onPath = contains(path, targetPath);
    switch (m.member.body()) {
      case Ast.Block b -> {
        Map<String, Sym> locals = new LinkedHashMap<>();
        for (Ast.Member l : b.locals()) {
          Sym ls = nestedSym(u, l, m, path, new Ctx(null, new LinkedHashMap<>(locals), outer, inline));
          locals.put(l.name(), ls);
          int i = tb.add(ls);
          if (targeted && !contains(ls.path, targetPath)) {
            if (onPath) u.skipped.add(new Skipped(ls.path, () -> typeStat(u, tb, i)));
          } else typeStat(u, tb, i);
        }
        try { tb.result = typePath(u, new Ctx(null, locals, outer, inline), b.result(), path); }
        catch (CyclicReference e) { tb.result = Type.err(e.getMessage()); }
      }
      case Ast.New n -> {
        Sym anon = newSym("<anon>$" + path, Kind.CLASS, u.name());
        anon.path = path; anon.defRunId = runId;
        ClassInfo ci = new ClassInfo();
        anon.info = ci;
        Ctx inner = new Ctx(anon, null, outer, inline);
        List<Integer> typed = new ArrayList<>();
        for (Ast.Member l : n.members()) {                   // the template's members exist once it is typed
          Sym ms = nestedSym(u, l, anon, path, inner);
          int i = tb.add(ms);
          if (targeted && !contains(ms.path, targetPath)) {
            if (onPath) u.skipped.add(new Skipped(ms.path, () -> { ci.decls.enter(ms); typeStat(u, tb, i); }));
          } else { ci.decls.enter(ms); typed.add(i); }
        }
        for (int i : typed) typeStat(u, tb, i);
        tb.result = Type.of(anon);
      }
    }
    tb.complete = true;
    return tb;
  }

  private Sym nestedSym(Unit u, Ast.Member l, Sym owner, String path, Ctx ctx) {
    Sym s = newSym(l.name(), Kind.DEF, u.name());
    s.owner = owner; s.defRunId = runId; s.member = l; s.mods = l.mods(); s.path = path + "." + l.name(); s.ctx = ctx;
    s.info = memberCompleter(u, s);
    return s;
  }

  /** Types statement `i` of a nested list: its signature, and its body against a declared type. */
  private void typeStat(Unit u, TypedBody tb, int i) {
    Sym s = tb.syms.get(i);
    Type t;
    try { t = typeOf(s); } catch (CyclicReference e) { t = Type.err(e.getMessage()); }
    checkBody(u, s, ctxOf(s), s.path);
    tb.set(i, t);
    counters.membersTyped++;
    signalDone(u, "local " + s.path, null);
  }

  /** A body typed against its declared type: a path, or a block or template (whose result is checked to type). */
  private void checkBody(Unit u, Sym s, Ctx ctx, String where) {
    Ast.Member m = s.member;
    if (m.inferred() || !m.hasBody()) return;
    Type b;
    if (m.body() != null) b = typedBodyOf(u, s).result;
    else try { b = typePath(u, ctx, m.path(), where); } catch (CyclicReference e) { b = Type.err(e.getMessage()); }
    if (b.isError()) report(u, new Problem("error", u.name(), where, b.error()));
  }

  /** Types the skipped nested statements on the path to `target` (all of them when null), splicing each into its typed
   * body; nested lists of a resumed statement are targeted in turn. */
  protected void resumeSkipped(Unit u, String target) {
    String saved = targetPath;
    targetPath = target;
    try {
      boolean more = true;
      while (more) {
        more = false;
        for (Skipped sk : new ArrayList<>(u.skipped)) if (target == null || contains(sk.path(), target)) { u.skipped.remove(sk); sk.resume().run(); more = true; }
      }
    } finally { targetPath = saved; }
  }

  public Sym lookupMember(Sym cls, String name) {
    cls = current(cls);
    ClassInfo ci = classInfo(cls);
    Sym m = ci.decls.term(name);
    if (m != null) return m;
    return ci.parent != null ? lookupMember(ci.parent, name) : null;
  }

  /** A top-level term by name: the one lookup of `typePath` that is not through a fact (the revisions kernel records it). */
  protected Sym topTerm(String name) { return toplevel.term(name); }

  public Type typeOf(Sym m) {
    if (m.kind == Kind.OBJECT) return Type.of(m);
    return (Type) force(m);
  }

  Type typePath(Unit u, Sym owner, List<String> path, String where) { return typePath(u, new Ctx(owner, null, null, false), path, where); }

  Type typePath(Unit u, Ctx ctx, List<String> path, String where) {
    String first = path.get(0);
    Sym s = null;
    for (Ctx c = ctx; c != null && s == null; c = c.outer()) {
      if (c.locals() != null) s = c.locals().get(first);
      if (s == null && c.cls() != null) s = lookupMember(c.cls(), first);
    }
    if (s == null) s = topTerm(first);
    if (s == null || s.kind == Kind.DEF && s.owner == null) return Type.err("not found: value " + first);
    Type t = refType(u, s);
    for (String name : path.subList(1, path.size())) {
      if (t.isError()) return t;
      if (t.cls == null) return Type.err("value " + name + " is not a member of " + t.show());
      Sym m = lookupMember(t.cls, name);
      if (m == null) {
        Sym factory = findImplicit(u, t, name);
        if (factory != null) m = lookupMember(factory.factoryOf, name);
      }
      if (m == null) return Type.err("value " + name + " is not a member of " + t.show());
      if (m.mods.contains("deprecated")) warn(u, where, "method " + name + " in " + m.owner.name + " is deprecated");
      t = refType(u, m);
    }
    return t;
  }

  /** The type of a reference: the symbol's, except through an inline method with a block or template body, whose
   * callers inline its typed body (`Inlines.bodyToInline`): a stub in it has no typed tree to copy (I28). */
  private Type refType(Unit u, Sym s) {
    Type t = typeOf(s);
    if (s.kind != Kind.DEF || s.member == null || s.member.body() == null || !s.mods.contains("inline")) return t;
    TypedBody tb = typedBodyOf(u, s);
    List<String> stubs = tb.stubs();
    if (!stubs.isEmpty()) return Type.err("type of TypeTree is not assigned: inline body of " + pathOf(s) + " has stubs " + Core.join(stubs));
    return tb.result;
  }

  /** scalac's implicit search over the implicits in scope, which are cached for the run (`implicitss`); a
   * cached candidate that the name no longer resolves to is shadowed and skipped. */
  public Sym findImplicit(Unit u, Type t, String name) {
    for (Sym cand : implicitCandidates(u)) {
      if (toplevel.term(cand.name) != cand) continue;   // shadowed (here: replaced)
      if (t.cls != null && t.cls.name.equals(cand.paramType) && lookupMember(cand.factoryOf, name) != null) return cand;
    }
    return null;
  }

  private List<Sym> implicitCandidates(Unit u) {
    if (u.implicitCache == null || u.implicitCacheRun != runId) {
      u.implicitCache = new ArrayList<>();
      for (Sym s : toplevel.syms()) if (s.factoryOf != null) u.implicitCache.add(s);
      u.implicitCacheRun = runId;
    }
    return u.implicitCache;
  }

  // ---- warnings ---------------------------------------------------------------------------------------

  private void warn(Unit u, String where, String msg) {
    Problem p = new Problem("warning", u.name(), where, msg);
    if (u.suppressionsKnown) { if (!u.suppressions.contains(where.substring(0, where.indexOf('.')))) u.problems.add(p); }
    else u.suspended.add(p);
  }

  /** `reportSuspendedMessages`: once the unit's `@nowarn`s are known, report what they do not cover, and
   * report later warnings directly. */
  private void reportSuspended(Unit u) {
    for (Problem p : u.suspended) if (!u.suppressions.contains(p.where().substring(0, p.where().indexOf('.')))) u.problems.add(p);
    u.suspended.clear();
    u.suppressionsKnown = true;
  }

  // ---- the typer --------------------------------------------------------------------------------------

  /** Type the unit's declarations in order; with a target, stop at it with a `TyperResult`. */
  public void typeUnit(Unit u, Target target) {
    Target savedTarget = u.target;
    Map<String, List<String>> bodies = new LinkedHashMap<>();
    u.target = target;
    try {
      for (Ast.Decl d : u.source.decls()) {
        typeDecl(u, d, bodies);
        addSynthetics(u, d.pos(), bodies);
      }
      if (target == null) { reportSuspended(u); u.bodies = bodies; u.typed = true; }
      else if (!policy.suspendTargetedWarnings) reportSuspended(u);
    } catch (TyperResult r) {
      if (!policy.suspendTargetedWarnings) reportSuspended(u);
      throw r;
    } finally {
      u.target = savedTarget;
    }
  }

  /** Targeted typing that resumes: type these declarations of the unit (by index, in the order given) that are not
   * typed yet, in the same run, adding them to the typed set; typing the last one finishes the unit. On a cancellation
   * `u.typing` is left at the declaration it unwound. */
  public void typeDecls(Unit u, List<Integer> idxs) {
    for (int i : idxs) {
      if (i >= u.source.decls().size() || u.typedDecls.get(i)) continue;
      Ast.Decl d = u.source.decls().get(i);
      u.typing = i;
      typeDecl(u, d, u.bodies);
      addSynthetics(u, d.pos(), u.bodies);
      u.typedDecls.set(i);
    }
    u.typing = -1;
    if (u.typedDecls.cardinality() >= u.source.decls().size() && !u.typed) { resumeSkipped(u, null); reportSuspended(u); u.typed = true; }
  }

  private void typeDecl(Unit u, Ast.Decl d, Map<String, List<String>> bodies) {
    Sym cls = d.isObject() ? toplevel.term(d.name()) : toplevel.type(d.name());
    if (d.isImplicit()) enterImplicitWrapper(u, cls, d);      // typedTemplate enters the body's symbols again
    ClassInfo ci = classInfo(cls);
    List<String> body = new ArrayList<>();
    if (d.isCase()) for (Ast.Param p : d.params()) body.add(p.name());
    for (Ast.Member m : d.members()) {
      Sym ms = ci.decls.term(m.name());
      typeOf(ms);
      if (!m.inferred() && m.path() != null) {                 // a body typed against its declared type
        Type b;
        try { b = typePath(u, cls, m.path(), d.name() + "." + m.name()); } catch (CyclicReference e) { b = Type.err(e.getMessage()); }
        if (b.isError()) u.problems.add(new Problem("error", u.name(), d.name() + "." + m.name(), b.error()));
      }
      if (m.body() != null) {                                   // a block or template: the typed-ahead tree, or typed now
        checkBody(u, ms, ctxOf(ms), d.name() + "." + m.name());
        bodies.put("body " + d.name() + "." + m.name(), typedBodyOf(u, ms).display);
      }
      body.add(m.name());
      counters.membersTyped++;
      signalDone(u, "member " + d.name() + "." + m.name(), new Target(d.name(), m.name()));
    }
    if (d.mods().contains("nowarn")) u.suppressions.add(d.name());  // known once the annotation is typed
    if (d.isCase() && !d.isObject()) {
      if (policy.uninterruptibleSynthesis) uninterruptible(() -> { finishMethodSynthesis(u, cls, ci, body); return null; });
      else finishMethodSynthesis(u, cls, ci, body);
    }
    counters.classesTyped++;
    bodies.computeIfAbsent(d.kind() + " " + d.name(), k -> new ArrayList<>()).addAll(body);  // after the merged synthetics typed with the case class
    signalDone(u, "class " + d.name(), null);
  }

  /** `addSyntheticMethods` for a case class: `equals`, `hashCode`, `toString`, one at a time, unless the class
   * already has them (`copy`, like `apply` and `unapply`, is the namer's). */
  private void finishMethodSynthesis(Unit u, Sym cls, ClassInfo ci, List<String> body) {
    if (ci.decls.term("equals") != null) {
      if (cls.synthesized != null && cls.synthesizedRun == runId) {
        body.addAll(cls.synthesized);                        // the trees a targeted check added
        if (u.target == null) cls.synthesized = null;
      }
      return;
    }
    List<String> added = burst(u, cls, ci, true);
    body.addAll(added);
    if (u.target != null && policy.keepSyntheticsForTargeted) { cls.synthesized = added; cls.synthesizedRun = runId; }
  }

  private List<String> burst(Unit u, Sym cls, ClassInfo ci, boolean signal) {
    List<String> added = new ArrayList<>();
    for (String name : List.of("equals", "hashCode", "toString")) {
      Sym s = newSym(name, Kind.DEF, u.name());
      s.owner = cls; s.synthetic = true; s.defRunId = runId;
      s.info = Type.builtin(name.equals("equals") ? "Boolean" : name.equals("hashCode") ? "Int" : "String");
      ci.decls.enter(s);
      added.add(name);
      if (signal) signalDone(u, "synth " + cls.name + "." + name, null);
    }
    return added;
  }

  /** The case-class burst outside the typer, for a class whose declaration a targeted run skipped; the trees are
   * kept for when the class is typed, as a targeted check's are (dotc spike, finding I13: `children` completes the
   * unit's classes in interactive mode, the presentation compiler completes the applies). */
  protected void synthesizeAhead(Unit u, Sym cls, ClassInfo ci) {
    if (ci.decls.term("equals") != null) return;
    cls.synthesized = burst(u, cls, ci, false); cls.synthesizedRun = runId;
  }

  /** `addSynthetics`: the synthetic trees from declaration `pos` join their owner's body and are consumed,
   * unless a targeted check is told to leave them for the full one. */
  private void addSynthetics(Unit u, int pos, Map<String, List<String>> bodies) {
    Runnable op = () -> {
      for (Map.Entry<Sym, Integer> e : new ArrayList<>(u.synthetics.entrySet())) {
        if (e.getValue() != pos) continue;
        Sym s = e.getKey();
        if (s.unlinked) continue;                         // scalac iterates the scope: a replaced factory's tree is never found
        if (s.kind == Kind.DEF) force(s);
        String owner = s.owner != null ? (s.owner.kind == Kind.OBJECT ? "object " : "class ") + s.owner.name : "<toplevel>";
        bodies.computeIfAbsent(owner, k -> new ArrayList<>()).add(s.name);
        if (u.target == null || !policy.keepSyntheticsForTargeted) u.synthetics.remove(s);
        signalDone(u, "synthetic " + owner + "." + s.name, null);
      }
    };
    if (policy.uninterruptibleSynthesis) uninterruptible(() -> { op.run(); return null; }); else op.run();
  }

  // ---- answers ----------------------------------------------------------------------------------------

  /** Type completion at the target member: the members of its type, with those reachable through an
   * implicit class marked `via`. */
  public String completionAnswer(Unit u, Target t) {
    Sym cls = toplevel.type(t.decl()) != null && !toplevel.type(t.decl()).unlinked ? toplevel.type(t.decl()) : toplevel.term(t.decl());
    if (cls == null) return "<no such declaration " + t.decl() + ">";
    String[] steps = t.member().split("\\.");
    Sym m = lookupMember(cls, steps[0]);
    if (m == null) return "<no such member " + t.member() + ">";
    Type tp;
    try { tp = typeOf(m); } catch (CyclicReference e) { tp = Type.err(e.getMessage()); }
    for (int k = 1; k < steps.length; k++) {                  // inside a body: the typed tree's statement, which may be a stub
      if (m.member == null || m.member.body() == null) return "<no such member " + t.member() + ">";
      TypedBody tb = typedBodyOf(u, m);
      int i = tb.names.indexOf(steps[k]);
      if (i < 0) return "<no such member " + t.member() + ">";
      if (tb.types.get(i) == null) return "<stub " + steps[k] + ">: <no members>";
      m = tb.syms.get(i); tp = tb.types.get(i);
    }
    if (tp.cls == null) return tp.show() + ": <no members>";
    TreeSet<String> names = new TreeSet<>(memberNames(tp.cls));
    for (Sym cand : implicitCandidates(u)) {
      if (toplevel.term(cand.name) != cand || !tp.cls.name.equals(cand.paramType)) continue;
      for (String n : memberNames(cand.factoryOf)) if (!names.contains(n)) names.add(n + " via " + cand.name);
    }
    return tp.show() + ": " + Core.join(names);
  }

  public List<String> memberNames(Sym cls) {
    List<String> r = new ArrayList<>();
    for (Sym c = current(cls); c != null; c = classInfo(c).parent == null ? null : current(classInfo(c).parent))
      for (Sym m : classInfo(c).decls.syms()) if (!r.contains(m.name)) r.add(m.name);
    return r;
  }

  public String unitAnswer(Unit u) {
    StringBuilder b = new StringBuilder();
    Set<String> printed = new HashSet<>();
    for (Ast.Decl d : u.source.decls()) {
      String key = d.kind() + " " + d.name();
      printed.add(key);
      b.append(key).append(": ").append(Core.join(new TreeSet<>(u.bodies.getOrDefault(key, List.of())))).append('\n');
      for (Ast.Member m : d.members()) {                        // a block's statements, a template's members, in order
        List<String> body = u.bodies.get("body " + d.name() + "." + m.name());
        if (body != null) b.append("body ").append(d.name()).append('.').append(m.name()).append(": ").append(Core.join(body)).append('\n');
      }
    }
    List<String> top = u.bodies.getOrDefault("<toplevel>", List.of());
    if (!top.isEmpty()) b.append("synthetic companions: ").append(Core.join(new TreeSet<>(top))).append('\n');
    for (Map.Entry<String, List<String>> e : u.bodies.entrySet())
      if (!printed.contains(e.getKey()) && !e.getKey().equals("<toplevel>") && !e.getKey().startsWith("body "))
        b.append(e.getKey()).append(" (synthetic): ").append(Core.join(new TreeSet<>(e.getValue()))).append('\n');
    TreeSet<String> ps = new TreeSet<>();
    for (Problem p : u.problems) ps.add(p.toString());
    for (String p : ps) b.append(p).append('\n');
    return b.toString();
  }
}
