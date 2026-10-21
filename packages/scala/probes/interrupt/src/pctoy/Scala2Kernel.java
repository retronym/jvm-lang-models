package pctoy;

import java.util.*;
import pctoy.Core.*;

/** scalac's interactive `Global`: one compiler thread types the loaded units in the background and, at
 * each `signalDone` where `interruptsEnabled && lockedCount == 0`, services the waiting requests *inside*
 * the type check in progress (`pollForWork`), against the same symbol table. A reload starts a new run and
 * abandons the background check with `FreshRunReq`; a targeted check stops at its target with
 * `TyperResult`. */
public final class Scala2Kernel extends Global implements Kernel {
  private final String name;
  private final Deque<Event> queue = new ArrayDeque<>();
  private final List<String> answers = new ArrayList<>();
  private boolean inBackground = false;
  private List<Ast.Source> sources = List.of();

  public Scala2Kernel(String name, Policy policy, Scheduler scheduler) { super(policy, scheduler); this.name = name; }

  @Override public String name() { return name; }
  @Override public long work() { return counters.total(); }

  @Override public void reload(List<Ast.Source> ss) { sources = ss; newRun(ss); }

  @Override public void send(Event e) { queue.add(e); }

  @Override protected void onEvent(Event e) { queue.add(e); }

  @Override protected void checkForMoreWork(String where) { pollForWork(); }

  @Override public List<String> drain() {
    while (true) {
      try {
        pollForWork();
        inBackground = true;
        for (Unit u : units.values()) if (!u.typed) typeUnit(u, null);
        inBackground = false;
        break;
      } catch (Cancelled c) {
        inBackground = false;                               // FreshRunReq: start over on the new run
      }
    }
    pollForWork();
    List<String> r = new ArrayList<>(answers);
    answers.clear();
    return r;
  }

  private void pollForWork() {
    while (!queue.isEmpty()) {
      Event e = queue.poll();
      switch (e) {
        case Event.Edit ed -> {
          List<Ast.Source> ss = new ArrayList<>();
          for (Ast.Source s : sources) ss.add(s.name().equals(ed.file()) ? Ast.parse(s.name(), ed.newText()) : s);
          reload(ss);
          queue.addFirst(new Event.Request(ed.ask()));
          if (inBackground) throw new Cancelled("FreshRunReq");
        }
        case Event.Request rq -> answers.add(serve(rq.ask()));
      }
    }
  }

  private String serve(Ask ask) {
    Unit u = units.get(ask.file());
    if (u == null) return "<no such file>";
    switch (ask) {
      case Ask.Completion c -> {
        Target t = new Target(c.decl(), c.member());
        if (u.typed) return completionAnswer(u, t);
        try { typeUnit(u, t); return "<target not reached>"; }
        catch (TyperResult r) { return r.answer; }
      }
      case Ask.LoadedTyped l -> {
        if (!u.typed) typeUnit(u, null);
        return unitAnswer(u);
      }
    }
  }
}
