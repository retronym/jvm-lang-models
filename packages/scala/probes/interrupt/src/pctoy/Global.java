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

  public record Target(String decl, String member) {}

  public static final class Unit {
    public Ast.Source source;
    public final Map<Sym, Integer> synthetics = new LinkedHashMap<>();  // synthetic tree → the declaration it came from
    public final List<Problem> problems = new ArrayList<>(), suspended = new ArrayList<>();
    public final Set<String> suppressions = new HashSet<>();
    public boolean suppressionsKnown;
    public Map<String, List<String>> bodies = new LinkedHashMap<>();
    public boolean typed;
    /** A session's typed prefix: the declarations typed so far by targeted runs (dotc spike). */
    public int typedUpTo;
    public Target target;
    public List<Sym> implicitCache; public int implicitCacheRun = -1;
    public String name() { return source.name(); }
    void reset(Ast.Source s) {
      source = s; synthetics.clear(); problems.clear(); suspended.clear(); suppressions.clear();
      suppressionsKnown = false; bodies = new LinkedHashMap<>(); typed = false; typedUpTo = 0; target = null; implicitCache = null;
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

  protected Global(Policy policy, Scheduler scheduler) { this.policy = policy; this.scheduler = scheduler; }

  // ---- hooks for the kernels --------------------------------------------------------------------------

  /** Called at every safepoint. `reached` is the target a targeted check has just typed, if any. */
  protected void signalDone(Unit unit, String where, Target reached) {
    Event ev = scheduler.at(where);
    if (ev != null) onEvent(ev);
    if (!interruptsEnabled || lockedCount > 0) return;
    if (reached != null && reached.equals(unit.target)) throw new TyperResult(completionAnswer(unit, reached));
    checkForMoreWork(where);
  }
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

  private Sym newSym(String name, Kind kind, String file) { return new Sym(name, kind, file, nextId++); }

  private static Kind kindOf(Ast.Decl d) {
    return switch (d.kind()) { case "object" -> Kind.OBJECT; case "trait" -> Kind.TRAIT; default -> Kind.CLASS; };
  }

  private void enterDecl(Unit u, Ast.Decl d) {
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
    sym.synthesized = null;
    if (d.isImplicit()) enterImplicitWrapper(u, sym, d);   // the namer enters the factory (enterClassDef)
  }

  /** A case class without an `object` of its own gets a synthetic companion; both get `apply` and `unapply`
   * whose trees wait in `unit.synthetics` until the typer adds them to the companion's body. */
  private void ensureCompanion(Unit u, Ast.Decl d) {
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
    for (String m : List.of("apply", "unapply")) {
      Sym s = newSym(m, Kind.DEF, u.name());
      s.owner = companion; s.synthetic = true; s.defRunId = runId;
      s.info = (Completer) self -> Type.of(cls);
      u.synthetics.put(s, d.pos());
    }
    Sym copy = newSym("copy", Kind.DEF, u.name());              // Namers.addCopyMethod: the namer's synthetic
    copy.owner = cls; copy.synthetic = true; copy.defRunId = runId;
    copy.info = (Completer) self -> Type.of(cls);
    u.synthetics.put(copy, d.pos());
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
        m.owner = cls; m.member = new Ast.Member(Set.of(), p.name(), p.tpe(), null, -1);
        m.info = memberCompleter(u, m);
        ci.decls.enter(m);
      }
      for (Ast.Member mem : d.members()) {
        Sym m = newSym(mem.name(), Kind.DEF, u.name());
        m.owner = cls; m.member = mem; m.mods = mem.mods();
        m.info = memberCompleter(u, m);
        ci.decls.enter(m);
      }
      for (Sym s : u.synthetics.keySet()) if (s.owner == cls) ci.decls.enter(s);
      return ci;
    };
  }

  private Completer memberCompleter(Unit u, Sym m) {
    return self -> {
      Ast.Member mem = m.member;
      Type t;
      if (!mem.inferred()) {
        Sym c = toplevel.type(mem.declared());
        t = c != null ? Type.of(c) : Type.err("not found: type " + mem.declared());
      } else {
        try { t = typePath(u, m.owner, mem.path(), m.owner.name + "." + m.name); }
        catch (CyclicReference e) { t = Type.err(e.getMessage()); }
      }
      if (t.isError()) u.problems.add(new Problem("error", u.name(), m.owner.name + "." + m.name, t.error()));
      signalDone(u, "rhs " + m.owner.name + "." + m.name, null);
      return t;
    };
  }

  public Sym lookupMember(Sym cls, String name) {
    cls = current(cls);
    ClassInfo ci = classInfo(cls);
    Sym m = ci.decls.term(name);
    if (m != null) return m;
    return ci.parent != null ? lookupMember(ci.parent, name) : null;
  }

  public Type typeOf(Sym m) {
    if (m.kind == Kind.OBJECT) return Type.of(m);
    return (Type) force(m);
  }

  private Type typePath(Unit u, Sym owner, List<String> path, String where) {
    String first = path.get(0);
    Sym s = lookupMember(owner, first);
    if (s == null) s = toplevel.term(first);
    if (s == null || s.kind == Kind.DEF && s.owner == null) return Type.err("not found: value " + first);
    Type t = typeOf(s);
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
      t = typeOf(m);
    }
    return t;
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

  /** Targeted typing that resumes: type the declarations from the unit's typed prefix up to `upTo` (inclusive), in
   * the same run, extending the prefix; typing the last one finishes the unit. */
  public void typeUnitUpTo(Unit u, int upTo) {
    for (int i = u.typedUpTo; i <= upTo && i < u.source.decls().size(); i++) {
      Ast.Decl d = u.source.decls().get(i);
      typeDecl(u, d, u.bodies);
      addSynthetics(u, d.pos(), u.bodies);
      u.typedUpTo = i + 1;
    }
    if (u.typedUpTo >= u.source.decls().size() && !u.typed) { reportSuspended(u); u.typed = true; }
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
    bodies.put(d.kind() + " " + d.name(), body);
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
    List<String> added = new ArrayList<>();
    for (String name : List.of("equals", "hashCode", "toString")) {
      Sym s = newSym(name, Kind.DEF, u.name());
      s.owner = cls; s.synthetic = true;
      s.info = Type.builtin(name.equals("equals") ? "Boolean" : name.equals("hashCode") ? "Int" : "String");
      ci.decls.enter(s);
      body.add(name); added.add(name);
      signalDone(u, "synth " + cls.name + "." + name, null);
    }
    if (u.target != null && policy.keepSyntheticsForTargeted) { cls.synthesized = added; cls.synthesizedRun = runId; }
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
    Sym m = lookupMember(cls, t.member());
    if (m == null) return "<no such member " + t.member() + ">";
    Type tp;
    try { tp = typeOf(m); } catch (CyclicReference e) { tp = Type.err(e.getMessage()); }
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
    }
    List<String> top = u.bodies.getOrDefault("<toplevel>", List.of());
    if (!top.isEmpty()) b.append("synthetic companions: ").append(Core.join(new TreeSet<>(top))).append('\n');
    for (Map.Entry<String, List<String>> e : u.bodies.entrySet())
      if (!printed.contains(e.getKey()) && !e.getKey().equals("<toplevel>"))
        b.append(e.getKey()).append(" (synthetic): ").append(Core.join(new TreeSet<>(e.getValue()))).append('\n');
    TreeSet<String> ps = new TreeSet<>();
    for (Problem p : u.problems) ps.add(p.toString());
    for (String p : ps) b.append(p).append('\n');
    return b.toString();
  }
}
