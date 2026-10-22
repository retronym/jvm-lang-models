package pctoy;

import java.util.*;
import java.util.function.Supplier;
import pctoy.Core.*;

/** Stage 3 of the toy (track-i.md §12, `ScalaTypes/ToyTree.lean`, `Query/Revision.lean`): facts that outlive
 * runs. An edit bumps the revision instead of starting a run. Symbols are re-entered by their name path (a
 * declaration, a member of one: the green tree's identity), so a node keeps its symbol and its facts across
 * edits, and the nodes themselves (a declaration's header and member names, a member) and the top-level scope
 * are inputs, set at each revision. Every fact remembers its value, the revision it was verified at, the
 * revision its value last changed at, and its trace: the facts its rule asked, in order, inputs and lookups
 * included, failed ones too (`lookup class C.n`, `lookup <toplevel>.term X`). A fact verified at an older
 * revision is re-validated on demand: its deps first, in the order asked, and its value reused if none changed
 * since; otherwise its rule runs, and a value equal to the old one keeps the old `changedAt` (backdating, Salsa's
 * `changed_at`). Typed members and typed declarations (`unit.bodies`) are facts in the same store, and a rule's
 * problems belong to its fact, so a reused fact reports them again.
 *
 * Every rule is a function of a symbol and the store, never a closure over a run, which is what lets a fact of
 * one revision be reused at a later one (§12, "What this says for dotc"). Re-validation is on demand across any
 * number of revisions: a node's change is an input's `changedAt`, so no footprint is needed. */
public final class Revisions extends Global implements Kernel {
  /** A fact: an input (rule null) or a rule's result. */
  static final class Fact {
    final String key, name; final Unit unit; final Supplier<Object> rule;
    Object value; String fp; int changedAt = -1, verifiedAt = -1; boolean computing;
    List<Fact> trace = List.of(); List<Problem> problems = List.of();
    Fact(String key, String name, Unit unit, Supplier<Object> rule) { this.key = key; this.name = name; this.unit = unit; this.rule = rule; }
    boolean isInput() { return rule == null; }
    boolean isLookup() { return key.startsWith("lookup "); }
    @Override public String toString() { return key; }
  }

  private final String name;
  private final Map<String, Fact> store = new LinkedHashMap<>();
  private final Map<Sym, Fact> symFacts = new HashMap<>();
  private final Map<String, Sym> byPath = new HashMap<>();
  private final Map<String, Set<String>> inputsOf = new HashMap<>();
  private final Map<String, Ast.Source> sources = new LinkedHashMap<>();
  private final Deque<String> toCompile = new ArrayDeque<>();
  private final Deque<Event> queue = new ArrayDeque<>();
  private final List<String> answers = new ArrayList<>();
  int rev = 0;
  private long computed = 0;
  /** The facts whose rules ran, in order. */
  final List<Fact> recomputed = new ArrayList<>();
  private Fact current; private List<Fact> curTrace; private List<Problem> curProblems;

  public Revisions(String name, Scheduler scheduler) { super(Policy.DOTC, scheduler); this.name = name; }

  @Override public String name() { return name; }
  /** The rules run, lookups not counted, so that the work compares with the other kernels' completers and members. */
  @Override public long work() { return computed; }
  @Override public void reload(List<Ast.Source> ss) { for (Ast.Source s : ss) { sources.put(s.name(), s); toCompile.add(s.name()); } }
  @Override public void send(Event e) { queue.push(e); }
  @Override protected void onEvent(Event e) {}
  @Override protected void checkForMoreWork(String where) {}
  @Override protected void signalDone(Unit unit, String where, Target reached) {}
  Collection<Fact> facts() { return store.values(); }

  @Override public List<String> drain() {
    while (!toCompile.isEmpty()) { String f = toCompile.poll(); revise(f); unitAnswerOf(units.get(f)); }   // the background: the whole unit
    while (!queue.isEmpty()) {
      switch (queue.pop()) {
        case Event.Edit ed -> { sources.put(ed.file(), Ast.parse(ed.file(), ed.newText())); revise(ed.file()); answers.add(serve(ed.ask())); }
        case Event.Request rq -> answers.add(serve(rq.ask()));
      }
    }
    List<String> r = new ArrayList<>(answers);
    answers.clear();
    return r;
  }

  private String serve(Ask ask) {
    Unit u = units.get(ask.file());
    if (u == null) return "<no such file>";
    return switch (ask) {
      case Ask.Completion c -> completionAnswer(u, new Target(c.decl(), c.member()));
      case Ask.LoadedTyped l -> unitAnswerOf(u);
    };
  }

  // ---- revisions: the namer by name path, and the inputs ---------------------------------------------------

  private static String key(Sym s) {
    return s.owner != null ? key(s.owner) + "." + s.name : (s.kind == Kind.DEF ? "factory" : s.kind.name().toLowerCase()) + " " + s.name;
  }

  /** A new revision of `file`: its declarations re-entered by name path, its nodes and the scope set as inputs. */
  private void revise(String file) {
    rev++; runId++;
    Ast.Source s = sources.get(file);
    Unit u = units.computeIfAbsent(file, k -> new Unit());
    u.reset(s);
    Set<Sym> keep = new HashSet<>();
    for (Ast.Decl d : s.decls()) {
      Sym cls = enterTop(u, d.isObject() ? Kind.OBJECT : d.kind().equals("trait") ? Kind.TRAIT : Kind.CLASS, d.name(), keep);
      cls.decl = d; cls.mods = d.mods(); cls.synthetic = false;
      if (d.isImplicit()) {                                   // the factory of an implicit class
        Sym f = enterTop(u, Kind.DEF, d.name(), keep);
        f.synthetic = true; f.factoryOf = cls; f.paramType = d.params().isEmpty() ? null : d.params().get(0).tpe(); f.info = Type.of(cls);
      }
    }
    for (Ast.Decl d : s.decls()) if (d.isCase() && !d.isObject() && !keep.contains(byPath.get("object " + d.name())))
      enterTop(u, Kind.OBJECT, d.name(), keep).synthetic = true;   // a synthetic companion
    for (Sym t : toplevel.syms()) if (t.file.equals(file) && !keep.contains(t)) toplevel.unlink(t);
    Set<String> seen = new LinkedHashSet<>();
    for (Ast.Decl d : s.decls()) {
      String k = d.kind() + " " + d.name();
      StringBuilder shape = new StringBuilder(d.mods() + " " + k + " " + d.params() + " extends " + d.parent() + " {");
      for (Ast.Member m : d.members()) shape.append(' ').append(m.mods()).append(' ').append(m.name());
      setInput(seen, "decl " + k, d, shape.toString());
      for (Ast.Param p : d.params()) setInput(seen, "member " + k + "." + p.name(), new Ast.Member(Set.of(), p.name(), p.tpe(), null, -1), "param " + p);
      for (Ast.Member m : d.members()) setInput(seen, "member " + k + "." + m.name(), m, m.mods() + " " + m);
    }
    for (String k : inputsOf.getOrDefault(file, Set.of())) if (!seen.contains(k)) setInput(null, k, null, "<absent>");
    inputsOf.put(file, seen);
    setInput(null, "scope", null, new TreeSet<>(toplevel.syms().stream().map(Sym::toString).toList()).toString());
  }

  private Sym enterTop(Unit u, Kind kind, String n, Set<Sym> keep) {
    Sym s = byPath.computeIfAbsent((kind == Kind.DEF ? "factory" : kind.name().toLowerCase()) + " " + n, k -> newSym(n, kind, u.name()));
    s.unlinked = false;
    toplevel.enter(s);
    keep.add(s);
    if (kind != Kind.DEF) symFacts.computeIfAbsent(s, x -> fact("decls " + key(s), s.name, u, () -> declsRule(u, s)));
    return s;
  }

  private void setInput(Set<String> seen, String key, Object v, String fp) {
    if (seen != null) seen.add(key);
    Fact f = store.computeIfAbsent(key, k -> new Fact(k, k, null, null));
    if (!fp.equals(f.fp)) f.changedAt = rev;
    f.value = v; f.fp = fp; f.verifiedAt = rev;
  }

  private Object read(String key) {
    return demand(store.computeIfAbsent(key, k -> { Fact f = new Fact(k, k, null, null); f.fp = "<absent>"; return f; }));
  }

  // ---- the store: demand, re-validation by trace, recomputation with backdating ----------------------------

  private Fact fact(String key, String n, Unit u, Supplier<Object> rule) { return store.computeIfAbsent(key, k -> new Fact(k, n, u, rule)); }

  private Object demand(Fact f) {
    if (curTrace != null && !curTrace.contains(f)) curTrace.add(f);
    validate(f);
    return f.value;
  }

  private void validate(Fact f) {
    if (f.isInput() || f.verifiedAt == rev) return;
    if (f.computing) throw new CyclicReference(f.name);
    if (f.verifiedAt >= 0 && depsUnchanged(f)) { f.verifiedAt = rev; return; }
    compute(f);
  }

  /** The deps re-validated in the order the rule asked them, up to the first that changed since `f` was verified. A
   * cycle met while re-validating counts as a change: the rule runs, and meets it as the black hole. */
  private boolean depsUnchanged(Fact f) {
    f.computing = true;
    try {
      for (Fact d : f.trace) {
        try { validate(d); } catch (CyclicReference e) { return false; }
        if (d.changedAt > f.verifiedAt) return false;
      }
      return true;
    } finally { f.computing = false; }
  }

  private void compute(Fact f) {
    Fact saved = current; List<Fact> savedTrace = curTrace; List<Problem> savedProblems = curProblems;
    List<Fact> trace = new ArrayList<>(); List<Problem> problems = new ArrayList<>();
    List<Problem> warnings = f.unit == null ? null : f.unit.suspended;    // `warn` suspends: the unit's @nowarns are applied at the answer
    int mark = warnings == null ? 0 : warnings.size();
    current = f; curTrace = trace; curProblems = problems; f.computing = true;
    try {
      Object v = f.rule.get();
      if (warnings != null) problems.addAll(warnings.subList(mark, warnings.size()));
      String fp = fp(v);
      if (!fp.equals(f.fp)) f.changedAt = rev;                 // else backdated: changedAt stays
      f.value = v; f.fp = fp; f.trace = trace; f.problems = problems; f.verifiedAt = rev;
      recomputed.add(f);
      if (!f.isLookup()) computed++;
    } finally {
      if (warnings != null) warnings.subList(mark, warnings.size()).clear();
      f.computing = false; current = saved; curTrace = savedTrace; curProblems = savedProblems;
    }
  }

  /** A value as compared for backdating: symbols by identity, which the name path keeps. */
  static String fp(Object v) {
    if (v == null) return "none";
    if (v instanceof Sym s) return s + (s.mods.contains("deprecated") ? " deprecated" : "") + (s.factoryOf != null ? "(" + s.paramType + ")" : "");
    if (v instanceof Type t) return t.cls() != null ? t.cls().toString() : t.show();
    if (v instanceof ClassInfo ci) return (ci.parent == null ? "" : "extends " + ci.parent + " ") + fp(ci.decls.syms());
    if (v instanceof List<?> l) return l.stream().map(Revisions::fp).toList().toString();
    return v.toString();
  }

  private void problem(String where, String msg) { curProblems.add(new Problem("error", current.unit.name(), where, msg)); }

  // ---- facts through Global: forcing, lookups -------------------------------------------------------------

  @Override public Object force(Sym s) { return s.info != null ? s.info : demand(symFacts.get(s)); }

  @Override public Sym lookupMember(Sym cls, String n) {
    Sym c = current(cls);
    return (Sym) demand(fact("lookup " + key(c) + "." + n, n, null, () -> {
      ClassInfo ci = classInfo(c);
      Sym m = ci.decls.term(n);
      return m != null || ci.parent == null ? m : lookupMember(ci.parent, n);
    }));
  }

  @Override protected Sym topTerm(String n) { return (Sym) demand(fact("lookup <toplevel>.term " + n, n, null, () -> { read("scope"); return toplevel.term(n); })); }
  private Sym topType(String n) { return (Sym) demand(fact("lookup <toplevel>.type " + n, n, null, () -> { read("scope"); return toplevel.type(n); })); }

  @Override public Sym findImplicit(Unit u, Type t, String n) {
    demand(fact("lookup <toplevel>.implicits", "implicits", null, () -> {
      read("scope");
      return toplevel.syms().stream().filter(s -> s.factoryOf != null).toList();
    }));
    return super.findImplicit(u, t, n);
  }

  // ---- the rules ------------------------------------------------------------------------------------------

  /** A class's members: its parameters if a case class, its members, and the synthetics, all the namer's here (the
   * typer's `equals`, `hashCode`, `toString` too, as I5 says they should be); a member keeps its symbol by name. */
  private Object declsRule(Unit u, Sym cls) {
    Ast.Decl d = (Ast.Decl) read("decl " + key(cls));
    ClassInfo ci = new ClassInfo();
    if (d != null && d.parent() != null) {
      Sym p = topType(d.parent());
      if (p == null) problem(d.name(), "not found: type " + d.parent()); else ci.parent = p;
    }
    if (d != null) {
      if (d.isCase()) for (Ast.Param p : d.params()) member(u, cls, ci, p.name(), Set.of(), null);
      for (Ast.Member m : d.members()) member(u, cls, ci, m.name(), m.mods(), null);
      if (d.isCase() && !d.isObject()) {
        member(u, cls, ci, "copy", Set.of(), Type.of(cls));
        member(u, cls, ci, "equals", Set.of(), Type.builtin("Boolean"));
        member(u, cls, ci, "hashCode", Set.of(), Type.builtin("Int"));
        member(u, cls, ci, "toString", Set.of(), Type.builtin("String"));
      }
    }
    if (cls.kind == Kind.OBJECT && read("decl class " + cls.name) instanceof Ast.Decl c && c.isCase()) {
      Sym cc = topType(cls.name);
      for (String n : List.of("apply", "unapply")) member(u, cls, ci, n, Set.of(), Type.of(cc));
    }
    return ci;
  }

  private void member(Unit u, Sym owner, ClassInfo ci, String n, Set<String> mods, Type info) {
    Sym m = byPath.computeIfAbsent(key(owner) + "." + n, k -> { Sym s = newSym(n, Kind.DEF, u.name()); s.owner = owner; return s; });
    m.mods = mods; m.synthetic = info != null; m.info = info;
    if (info == null) symFacts.computeIfAbsent(m, s -> fact("type " + key(s), s.name, u, () -> typeRule(u, s)));
    ci.decls.enter(m);
  }

  private Type typeBody(Unit u, Sym m, List<String> path) {
    try { return typePath(u, m.owner, path, m.owner.name + "." + m.name); } catch (CyclicReference e) { return Type.err(e.getMessage()); }
  }

  /** A member's type: declared, or inferred from its path. */
  private Object typeRule(Unit u, Sym m) {
    Ast.Member mem = (Ast.Member) read("member " + key(m));
    if (mem == null) return Type.err("no such member " + m.name);
    Type t;
    if (mem.declared() != null) { Sym c = topType(mem.declared()); t = c != null ? Type.of(c) : Type.err("not found: type " + mem.declared()); }
    else t = typeBody(u, m, mem.path());
    if (t.isError()) problem(m.owner.name + "." + m.name, t.error());
    return t;
  }

  /** A typed member: its type and, when declared with a body, the body typed against it. */
  private Object typedRule(Unit u, Sym m) {
    Type sig = typeOf(m);
    Ast.Member mem = (Ast.Member) read("member " + key(m));
    if (mem == null || mem.declared() == null || mem.path() == null) return fp(sig);
    Type b = typeBody(u, m, mem.path());
    if (b.isError()) problem(m.owner.name + "." + m.name, b.error());
    return fp(sig) + " = " + fp(b);
  }

  /** A typed declaration: its body as `typeDecl` and `addSynthetics` leave it in `unit.bodies`, each member typed. */
  private Object bodyRule(Unit u, Sym cls) {
    Ast.Decl d = (Ast.Decl) read("decl " + key(cls));
    Map<String, List<String>> out = new LinkedHashMap<>();
    if (d == null) return out;
    ClassInfo ci = classInfo(cls);
    List<String> body = new ArrayList<>();
    if (d.isCase()) for (Ast.Param p : d.params()) body.add(p.name());
    for (Ast.Member m : d.members()) {
      Sym ms = ci.decls.term(m.name());
      demand(fact("typed " + key(ms), ms.name, u, () -> typedRule(u, ms)));
      body.add(m.name());
    }
    out.put(d.kind() + " " + d.name(), body);
    if (d.isImplicit()) out.computeIfAbsent("<toplevel>", k -> new ArrayList<>()).add(d.name());
    if (d.isCase() && !d.isObject()) {
      body.addAll(List.of("equals", "hashCode", "toString"));
      if (read("decl object " + d.name()) == null) out.computeIfAbsent("<toplevel>", k -> new ArrayList<>()).add(d.name());
      out.computeIfAbsent("object " + d.name(), k -> new ArrayList<>()).addAll(List.of("apply", "unapply"));
      body.add("copy");
    }
    return out;
  }

  /** The whole unit: every declaration's typed form, and the problems of every fact of the unit they reach. */
  @SuppressWarnings("unchecked")
  private String unitAnswerOf(Unit u) {
    Map<String, List<String>> bodies = new LinkedHashMap<>();
    Deque<Fact> todo = new ArrayDeque<>();
    Set<String> nowarn = new HashSet<>();
    for (Ast.Decl d : u.source.decls()) {
      Sym cls = byPath.get(d.kind() + " " + d.name());
      Fact f = fact("body " + key(cls), d.name(), u, () -> bodyRule(u, cls));
      ((Map<String, List<String>>) demand(f)).forEach((k, v) -> {
        bodies.computeIfAbsent(k, x -> new ArrayList<>()).addAll(v);   // typeDecl's, after the merged synthetics
      });
      todo.add(f);
      if (d.mods().contains("nowarn")) nowarn.add(d.name());
    }
    u.problems.clear();
    Set<Fact> seen = new HashSet<>();
    while (!todo.isEmpty()) {
      Fact f = todo.pop();
      if (!seen.add(f)) continue;
      todo.addAll(f.trace);
      if (f.unit == u) for (Problem p : f.problems)
        if (p.kind().equals("error") || !nowarn.contains(p.where().substring(0, p.where().indexOf('.')))) u.problems.add(p);
    }
    u.bodies = bodies;
    return unitAnswer(u);
  }
}
