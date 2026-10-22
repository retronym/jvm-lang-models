package pctoy;

import java.util.*;
import java.util.regex.*;

/** The toy language: classes, objects and traits with members; no expressions.
 *
 * <pre>
 * file   := decl*
 * decl   := mods ('class' | 'object' | 'trait') Name ('(' Name ':' Name (',' Name ':' Name)* ')')? ('extends' Name)? '{' member* '}'
 * mods   := ('case' | 'implicit' | 'nowarn' | 'deprecated' | 'inline')*
 * member := mods 'def' Name (':' Name)? ('=' body)?          (a type, a body, or both)
 * body   := path | '{' member* path '}' | 'new' '{' member* '}'
 * path   := Name ('.' Name)*
 * </pre>
 * (`;` is whitespace.)
 *
 * A member's type is declared (`def m: T`, with or without a body `= a.b.c` typed against it) or inferred
 * from a path (`def m = a.b.c`): the first name is
 * a member of the enclosing class (own or inherited) or a top-level object; each further name is a member
 * of the type so far, or, failing that, a member of an implicit class in scope that takes that type.
 * Inference is what forces other facts, so this is enough for cycles, levels and interleavings.
 * `case` classes get synthetic `copy`, `equals`, `hashCode`, `toString` and a companion with `apply` and
 * `unapply`; an `implicit` class gets a synthetic factory method of its own name next to it.
 *
 * Nested statement lists, for the findings about trees typed off the path to a target (I21, I25, I28): a block
 * `{ def a: T; def b = a; b }` has locals, each visible to the later ones and to its result path (lookup: the
 * locals first, then as above), and the block's type is its result path's; `new { members }` is a fresh anonymous
 * class `<anon>$Decl.member` whose member set is what typing its template enters, not the namer's; an `inline def`'s
 * callers read its type from its typed body, a value they reuse. A completion target may name a local or an
 * anonymous class's member by its path, `Decl.m.b`. */
public final class Ast {
  private Ast() {}

  public record Source(String name, String text, List<Decl> decls) {}
  public record Param(String name, String tpe) {}
  /** A member's body: a path (`Member.path`, with `body` null), or a block or an anonymous class (`body`). */
  public sealed interface Body {}
  public record Block(List<Member> locals, List<String> result) implements Body {
    @Override public String toString() { StringBuilder b = new StringBuilder("{"); for (Member m : locals) b.append(' ').append(m).append(';'); return b.append(' ').append(String.join(".", result)).append(" }").toString(); }
  }
  public record New(List<Member> members) implements Body {
    @Override public String toString() { StringBuilder b = new StringBuilder("new {"); for (Member m : members) b.append(' ').append(m).append(';'); return b.append(" }").toString(); }
  }
  public record Member(Set<String> mods, String name, String declared, List<String> path, int pos, Body body) {
    public Member(Set<String> mods, String name, String declared, List<String> path, int pos) { this(mods, name, declared, path, pos, null); }
    public boolean inferred() { return declared == null; }
    public boolean hasBody() { return path != null || body != null; }
    @Override public String toString() { return "def " + name + (declared != null ? ": " + declared : "") + (path != null ? " = " + String.join(".", path) : body != null ? " = " + body : ""); }
  }
  public record Decl(Set<String> mods, String kind, String name, List<Param> params, String parent, List<Member> members, int pos) {
    public boolean isCase() { return mods.contains("case"); }
    public boolean isImplicit() { return mods.contains("implicit"); }
    public boolean isObject() { return kind.equals("object"); }
  }

  public static Source parse(String name, String text) {
    return new Parser(text).file(name);
  }

  private static final class Parser {
    private static final Pattern TOKEN = Pattern.compile("[\\s;]+|//[^\\n]*|([A-Za-z_][A-Za-z0-9_]*|[(){}:=.,])");
    private final List<String> toks = new ArrayList<>();
    private final List<Integer> offs = new ArrayList<>();
    private int i = 0;
    private final String text;

    Parser(String text) {
      this.text = text;
      Matcher m = TOKEN.matcher(text);
      int at = 0;
      while (at < text.length()) {
        if (!m.find(at) || m.start() != at) throw new IllegalArgumentException("bad token at " + at + ": " + text.substring(at, Math.min(at + 10, text.length())));
        if (m.group(1) != null) { toks.add(m.group(1)); offs.add(m.start()); }
        at = m.end();
      }
    }

    private String peek() { return i < toks.size() ? toks.get(i) : null; }
    private String next() { return toks.get(i++); }
    private boolean accept(String s) { if (s.equals(peek())) { i++; return true; } return false; }
    private String expect(String s) { if (!accept(s)) throw new IllegalArgumentException("expected " + s + " at " + (i < offs.size() ? offs.get(i) : -1) + ", got " + peek()); return s; }
    private String ident() { String t = next(); if (!Character.isJavaIdentifierStart(t.charAt(0))) throw new IllegalArgumentException("expected identifier, got " + t); return t; }

    Source file(String name) {
      List<Decl> decls = new ArrayList<>();
      while (peek() != null) decls.add(decl(decls.size()));
      return new Source(name, text, List.copyOf(decls));
    }

    private static final Set<String> MODS = Set.of("case", "implicit", "nowarn", "deprecated", "inline");

    private Set<String> mods() {
      Set<String> mods = new LinkedHashSet<>();
      while (peek() != null && MODS.contains(peek())) mods.add(next());
      return mods;
    }

    private Decl decl(int pos) {
      Set<String> mods = mods();
      String kind = next();
      if (!Set.of("class", "object", "trait").contains(kind)) throw new IllegalArgumentException("expected class/object/trait, got " + kind);
      String name = ident();
      List<Param> params = new ArrayList<>();
      if (accept("(")) {
        do { String p = ident(); expect(":"); params.add(new Param(p, ident())); } while (accept(","));
        expect(")");
      }
      String parent = accept("extends") ? ident() : null;
      List<Member> members = new ArrayList<>();
      expect("{");
      while (!accept("}")) members.add(member(members.size()));
      return new Decl(mods, kind, name, List.copyOf(params), parent, List.copyOf(members), pos);
    }

    private Member member(int pos) {
      Set<String> mods = mods();
      expect("def");
      String name = ident();
      String declared = accept(":") ? ident() : null;
      if (declared != null && !accept("=")) return new Member(mods, name, declared, null, pos);
      if (declared == null) expect("=");
      if (accept("{")) {
        List<Member> locals = new ArrayList<>();
        while (MODS.contains(peek()) || "def".equals(peek())) locals.add(member(locals.size()));
        List<String> result = path();
        expect("}");
        return new Member(mods, name, declared, null, pos, new Block(List.copyOf(locals), result));
      }
      if (accept("new")) {
        List<Member> members = new ArrayList<>();
        expect("{");
        while (!accept("}")) members.add(member(members.size()));
        return new Member(mods, name, declared, null, pos, new New(List.copyOf(members)));
      }
      return new Member(mods, name, declared, path(), pos);
    }

    private List<String> path() {
      List<String> path = new ArrayList<>();
      path.add(ident());
      while (accept(".")) path.add(ident());
      return List.copyOf(path);
    }
  }
}
