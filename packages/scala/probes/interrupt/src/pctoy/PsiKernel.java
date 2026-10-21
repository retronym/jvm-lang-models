package pctoy;

import java.util.*;
import java.util.function.Supplier;
import pctoy.Core.*;

/** IntelliJ's PSI, as the Scala plugin uses it: no runs and no symbol table. Declarations are stubs,
 * always available from the parse (level 0); everything else is a pure function of the stubs, cached under
 * a modification count (`CachedValue`, the plugin's `cachedInUserData`) and computed by whichever read
 * action asks first. A write action (an edit) cancels every read action at its next `checkCanceled`
 * (`ProcessCanceledException`), bumps the count, and the readers start over. Re-entry is prevented by
 * `RecursionManager`: the inner computation gets `null`, and nothing computed above the re-entered frame is
 * cached (`StackStamp.mayCacheNow`). Requests are read actions of their own: they run concurrently with
 * the daemon's, here inline on a fresh recursion stack. */
public final class PsiKernel implements Kernel {
  private final String name;
  private final Scheduler scheduler;
  private final Map<String, Ast.Source> files = new LinkedHashMap<>();
  private final Deque<Event> queue = new ArrayDeque<>();
  private final List<String> answers = new ArrayList<>();
  private final Counters counters = new Counters();
  private long modCount = 0;
  private Event.Edit pendingWrite;
  private boolean inReadAction = false, dirty = false;

  public PsiKernel(String name, Scheduler scheduler) { this.name = name; this.scheduler = scheduler; }

  @Override public String name() { return name; }
  @Override public long work() { return counters.total(); }
  @Override public void reload(List<Ast.Source> ss) { for (Ast.Source s : ss) files.put(s.name(), s); modCount++; caches.clear(); dirty = true; }
  @Override public void send(Event e) { queue.add(e); }

  // ---- stubs ------------------------------------------------------------------------------------------

  /** A member element: a declared one, or a light synthetic one. */
  record Mem(String owner, String name, Set<String> mods, String declared, List<String> path, boolean synthetic, String file) {
    boolean inferred() { return path != null; }
  }
  record DeclRef(Ast.Decl decl, String file) {}

  private DeclRef typeDecl(String name) {
    for (Ast.Source s : files.values()) for (Ast.Decl d : s.decls()) if (!d.isObject() && d.name().equals(name)) return new DeclRef(d, s.name());
    return null;
  }
  private DeclRef termDecl(String name) {
    for (Ast.Source s : files.values()) for (Ast.Decl d : s.decls()) if (d.isObject() && d.name().equals(name)) return new DeclRef(d, s.name());
    DeclRef c = typeDecl(name);                        // a case class's synthetic companion: a light element
    if (c != null && c.decl().isCase()) return new DeclRef(new Ast.Decl(Set.of(), "object", name, List.of(), null, List.of(), c.decl().pos()), c.file());
    return null;
  }

  // ---- caches and the recursion manager ---------------------------------------------------------------

  record Stamped(long mod, Object value) {}
  private final Map<String, Stamped> caches = new HashMap<>();

  private static final class Frame { final String key; boolean tainted; Frame(String k) { key = k; } }
  private List<Frame> stack = new ArrayList<>();

  /** `RecursionManager.doPreventingRecursion`: null on re-entry, and no caching above the re-entered frame. */
  private <T> T preventingRecursion(String key, Supplier<T> computation) {
    for (int i = 0; i < stack.size(); i++) if (stack.get(i).key.equals(key)) {
      for (int j = i + 1; j < stack.size(); j++) stack.get(j).tainted = true;
      return null;
    }
    Frame f = new Frame(key);
    stack.add(f);
    try { return computation.get(); } finally { stack.remove(stack.size() - 1); }
  }

  /** A cached value keyed by the modification count, computed under a recursion guard and stored only when
   * the stamp allows it (`mayCacheNow`). */
  @SuppressWarnings("unchecked")
  private <T> T cached(String key, Supplier<T> compute, T onRecursion) {
    Stamped s = caches.get(key);
    if (s != null && s.mod == modCount) return (T) s.value;
    boolean[] mayCache = { true };
    T v = preventingRecursion(key, () -> {
      counters.completers++;
      Frame mine = stack.get(stack.size() - 1);
      T r = compute.get();
      mayCache[0] = !mine.tainted;
      return r;
    });
    if (v == null) return onRecursion;
    if (mayCache[0]) caches.put(key, new Stamped(modCount, v));
    return v;
  }

  // ---- facts ------------------------------------------------------------------------------------------

  private List<Mem> members(boolean term, String name) {
    return cached((term ? "term:" : "type:") + name, () -> {
      DeclRef r = term ? termDecl(name) : typeDecl(name);
      if (r == null) return List.of();
      Ast.Decl d = r.decl();
      List<Mem> ms = new ArrayList<>();
      if (d.isCase()) for (Ast.Param p : d.params()) ms.add(new Mem(name, p.name(), Set.of(), p.tpe(), null, false, r.file()));
      for (Ast.Member m : d.members()) ms.add(new Mem(name, m.name(), m.mods(), m.declared(), m.path(), false, r.file()));
      if (d.isCase() && !term) for (String s : List.of("copy", "equals", "hashCode", "toString"))
        ms.add(new Mem(name, s, Set.of(), s.equals("copy") ? name : "<builtin>", null, true, r.file()));
      DeclRef cls;
      if (term && (cls = typeDecl(name)) != null && cls.decl().isCase())
        for (String s : List.of("apply", "unapply")) ms.add(new Mem(name, s, Set.of(), name, null, true, r.file()));
      if (!term && d.parent() != null) for (Mem pm : members(false, d.parent())) if (ms.stream().noneMatch(x -> x.name().equals(pm.name()))) ms.add(pm);
      return ms;
    }, List.of());
  }

  private Mem member(boolean term, String owner, String name) {
    for (Mem m : members(term, owner)) if (m.name().equals(name)) return m;
    return null;
  }

  private record Res(Global.Type type, List<Problem> problems) {}

  /** The type of a member, with the problems its reference raises; `Res` is what the annotator shows. */
  private Res memberType(boolean term, String owner, String name) {
    return cached("type:" + (term ? "term " : "") + owner + "." + name, () -> {
      Mem m = member(term, owner, name);
      if (m == null) return new Res(Global.Type.err("not found: value " + name), List.of());
      String where = owner + "." + name;
      List<Problem> ps = new ArrayList<>();
      Global.Type t;
      if (!m.inferred()) {
        if (m.declared().equals("<builtin>")) t = Global.Type.builtin("Any");
        else t = typeDecl(m.declared()) != null ? typeRef(m.declared()) : Global.Type.err("not found: type " + m.declared());
      } else t = typePath(term, owner, m.path(), where, ps);
      if (t.isError()) ps.add(new Problem("error", m.file(), where, t.error()));
      checkCanceled("rhs " + where);
      return new Res(t, ps);
    }, new Res(Global.Type.err("recursive value " + name), List.of()));
  }

  /** Types are names here: a class is identified by its stub, there is no symbol to be stale. */
  private Global.Type typeRef(String cls) { return new Global.Type(null, cls, null); }

  private Global.Type typePath(boolean term, String owner, List<String> path, String where, List<Problem> ps) {
    String first = path.get(0);
    Global.Type t;
    if (member(term, owner, first) != null) t = memberType(term, owner, first).type();
    else if (termDecl(first) != null) t = new Global.Type(null, "object " + first, null);
    else return Global.Type.err("not found: value " + first);
    for (String n : path.subList(1, path.size())) {
      if (t.isError()) return t;
      boolean objType = t.builtin().startsWith("object ");
      String cls = objType ? t.builtin().substring(7) : t.builtin();
      Mem m = member(objType, cls, n);
      if (m == null && !objType) { Mem f = findImplicit(cls, n); if (f != null) m = f; }
      if (m == null) return Global.Type.err("value " + n + " is not a member of " + (objType ? first : cls));
      if (m.mods().contains("deprecated")) {
        DeclRef enclosing = term ? termDecl(owner) : typeDecl(owner);
        if (enclosing == null || !enclosing.decl().mods().contains("nowarn"))
          ps.add(new Problem("warning", enclosing == null ? "?" : enclosing.file(), where, "method " + n + " in " + m.owner() + " is deprecated"));
      }
      t = memberType(m.owner().equals(cls) && objType, m.owner(), n).type();
    }
    return t;
  }

  private List<DeclRef> implicitClasses() {
    return cached("implicits", () -> {
      List<DeclRef> r = new ArrayList<>();
      for (Ast.Source s : files.values()) for (Ast.Decl d : s.decls()) if (d.isImplicit()) r.add(new DeclRef(d, s.name()));
      return r;
    }, List.of());
  }

  private Mem findImplicit(String cls, String name) {
    for (DeclRef r : implicitClasses())
      if (!r.decl().params().isEmpty() && r.decl().params().get(0).tpe().equals(cls)) { Mem m = member(false, r.decl().name(), name); if (m != null) return m; }
    return null;
  }

  // ---- read actions, the daemon and requests -------------------------------------------------------

  private void checkCanceled(String where) {
    Event ev = scheduler.at(where);
    if (ev != null) {
      switch (ev) {
        case Event.Request rq -> answers.add(readAction(() -> serve(rq.ask())));   // another thread's read action
        case Event.Edit ed -> pendingWrite = ed;                                  // a write action waits
      }
    }
    if (pendingWrite != null && inReadAction) throw new Cancelled("write action pending at " + where);
  }

  /** A read action on its own thread: a fresh recursion stack, the shared caches. */
  private <T> T readAction(Supplier<T> op) {
    List<Frame> saved = stack; boolean savedIn = inReadAction;
    stack = new ArrayList<>(); inReadAction = true;
    try { return op.get(); } finally { stack = saved; inReadAction = savedIn; }
  }

  private void daemon() {
    for (Ast.Source s : files.values()) for (Ast.Decl d : s.decls()) {
      for (Mem m : members(d.isObject(), d.name())) { memberType(d.isObject(), d.name(), m.name()); checkCanceled("member " + d.name() + "." + m.name()); }
      checkCanceled("class " + d.name());
    }
  }

  @Override public List<String> drain() {
    while (true) {
      if (dirty) {                                               // the daemon re-annotates after a change
        try { readAction(() -> { daemon(); return null; }); dirty = false; }
        catch (Cancelled c) {}
      }
      if (pendingWrite != null) {                                // the write action runs, then readers restart
        Event.Edit ed = pendingWrite; pendingWrite = null;
        files.put(ed.file(), Ast.parse(ed.file(), ed.newText())); modCount++; dirty = true;
        queue.addFirst(new Event.Request(ed.ask()));
        continue;
      }
      if (!queue.isEmpty()) {
        Event e = queue.poll();
        switch (e) {
          case Event.Edit ed -> { pendingWrite = ed; continue; }
          case Event.Request rq -> answers.add(readAction(() -> serve(rq.ask())));
        }
        continue;
      }
      break;
    }
    List<String> r = new ArrayList<>(answers);
    answers.clear();
    return r;
  }

  private String serve(Ask ask) {
    if (!files.containsKey(ask.file())) return "<no such file>";
    switch (ask) {
      case Ask.Completion c -> {
        boolean term = termDecl(c.decl()) != null && typeDecl(c.decl()) == null;
        Global.Type t = memberType(term, c.decl(), c.member()).type();
        if (t.isError()) return t.show() + ": <no members>";
        boolean objType = t.builtin().startsWith("object ");
        String cls = objType ? t.builtin().substring(7) : t.builtin();
        TreeSet<String> names = new TreeSet<>();
        for (Mem m : members(objType, cls)) names.add(m.name());
        if (!objType) for (DeclRef r : implicitClasses())
          if (!r.decl().params().isEmpty() && r.decl().params().get(0).tpe().equals(cls))
            for (Mem m : members(false, r.decl().name())) if (!names.contains(m.name())) names.add(m.name() + " via " + r.decl().name());
        return cls + ": " + Core.join(names);
      }
      case Ask.LoadedTyped l -> {
        Ast.Source s = files.get(l.file());
        StringBuilder b = new StringBuilder();
        TreeSet<String> problems = new TreeSet<>();
        List<String> companions = new ArrayList<>();
        for (Ast.Decl d : s.decls()) {
          TreeSet<String> body = new TreeSet<>();
          for (Mem m : members(d.isObject(), d.name())) if (m.owner().equals(d.name())) { body.add(m.name()); for (Problem p : memberType(d.isObject(), d.name(), m.name()).problems()) problems.add(p.toString()); }
          b.append(d.kind()).append(' ').append(d.name()).append(": ").append(Core.join(body)).append('\n');
          if (d.isCase() && !d.isObject() && s.decls().stream().noneMatch(o -> o.isObject() && o.name().equals(d.name()))) companions.add(d.name());
        }
        if (!companions.isEmpty()) b.append("synthetic companions: ").append(Core.join(companions)).append('\n');
        for (String c : companions) { TreeSet<String> body = new TreeSet<>(); for (Mem m : members(true, c)) body.add(m.name()); b.append("object ").append(c).append(" (synthetic): ").append(Core.join(body)).append('\n'); }
        for (String p : problems) b.append(p).append('\n');
        return b.toString();
      }
    }
  }
}
