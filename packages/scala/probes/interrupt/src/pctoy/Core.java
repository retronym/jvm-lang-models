package pctoy;

import java.util.*;

/** What the three kernels share: requests and answers, the interleaving scheduler, work counters, and the
 * exceptions that unwind a type check. */
public final class Core {
  private Core() {}

  /** A request to the presentation compiler. */
  public sealed interface Ask {
    String file();
    /** Type completion at `member` of `decl`: the members of `decl` as the compiler sees them when the
     * target is reached (scalac: a targeted type check that stops at the target). */
    record Completion(String file, String decl, String member) implements Ask {
      @Override public String toString() { return "completion " + file + ":" + decl + "." + member; }
    }
    /** The fully typed unit: each declaration's body, and the problems reported. */
    record LoadedTyped(String file) implements Ask {
      @Override public String toString() { return "loadedTyped " + file; }
    }
  }

  /** An event injected at a safepoint by the harness. */
  public sealed interface Event {
    record Request(Ask ask) implements Event { @Override public String toString() { return ask.toString(); } }
    /** The file's text is replaced (the user typed), then `ask` is sent. */
    record Edit(String file, String newText, Ask ask) implements Event { @Override public String toString() { return "edit " + file + " then " + ask; } }
  }

  /** A diagnostic. */
  public record Problem(String kind, String file, String where, String msg) {
    @Override public String toString() { return kind + " " + file + ":" + where + ": " + msg; }
  }

  /** The interface of a kernel: a presentation compiler for the toy language. */
  public interface Kernel {
    String name();
    /** Load (or replace) sources; background work starts at the next `drain`. */
    void reload(List<Ast.Source> sources);
    /** Send a request; answered synchronously or at a later safepoint, see `drain`. */
    void send(Event e);
    /** Run background work and pending requests to completion; returns the answers in request order. */
    List<String> drain();
    /** Facts computed so far (completers run, members typed): the work done. */
    long work();
  }

  /** Counts safepoints, and fires the injected event at the chosen one. Kernels call `safepoint` from
   * their typers wherever they could service a request or observe a cancellation. */
  public static final class Scheduler {
    public int count = 0;
    public int fireAt = -1;
    public Event pending;
    public boolean fired = false;
    private final List<String> trace = new ArrayList<>();
    public void reset(int fireAt, Event e) { count = 0; this.fireAt = fireAt; pending = e; fired = false; trace.clear(); }
    /** Returns the event to inject at this safepoint, or null. */
    public Event at(String where) {
      trace.add(where);
      int k = count++;
      if (k == fireAt && !fired) { fired = true; return pending; }
      return null;
    }
    public List<String> trace() { return trace; }
  }

  public static final class Counters {
    public long completers = 0, membersTyped = 0, classesTyped = 0;
    public long total() { return completers + membersTyped; }
  }

  /** scalac's `CyclicReference`, dotc's too: a fact asked while it is being computed. */
  public static final class CyclicReference extends RuntimeException {
    public final String sym;
    public CyclicReference(String sym) { super("cyclic reference involving " + sym, null, false, false); this.sym = sym; }
  }

  /** scalac's `TyperResult`: a targeted type check has reached its target and unwinds with the answer. */
  public static final class TyperResult extends RuntimeException {
    public final String answer;
    public TyperResult(String answer) { super("typer result", null, false, false); this.answer = answer; }
  }

  /** scalac's `FreshRunReq` / `CancelException`, IntelliJ's `ProcessCanceledException`: the work is abandoned. */
  public static final class Cancelled extends RuntimeException {
    public Cancelled(String why) { super(why, null, false, false); }
  }

  public static String join(Collection<?> xs) {
    StringBuilder b = new StringBuilder();
    for (Object x : xs) { if (b.length() > 0) b.append(' '); b.append(x); }
    return b.toString();
  }
}
