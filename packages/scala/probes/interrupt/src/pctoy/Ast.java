package pctoy;

import java.util.*;
import java.util.regex.*;

/** The toy language: classes, objects and traits with members; no expressions.
 *
 * <pre>
 * file   := decl*
 * decl   := mods ('class' | 'object' | 'trait') Name ('(' Name ':' Name (',' Name ':' Name)* ')')? ('extends' Name)? '{' member* '}'
 * mods   := ('case' | 'implicit' | 'nowarn' | 'deprecated')*
 * member := mods 'def' Name (':' Name ('=' Name ('.' Name)*)? | '=' Name ('.' Name)*)
 * </pre>
 *
 * A member's type is declared (`def m: T`, with or without a body `= a.b.c` typed against it) or inferred
 * from a path (`def m = a.b.c`): the first name is
 * a member of the enclosing class (own or inherited) or a top-level object; each further name is a member
 * of the type so far, or, failing that, a member of an implicit class in scope that takes that type.
 * Inference is what forces other facts, so this is enough for cycles, levels and interleavings.
 * `case` classes get synthetic `copy`, `equals`, `hashCode`, `toString` and a companion with `apply` and
 * `unapply`; an `implicit` class gets a synthetic factory method of its own name next to it. */
public final class Ast {
  private Ast() {}

  public record Source(String name, String text, List<Decl> decls) {}
  public record Param(String name, String tpe) {}
  public record Member(Set<String> mods, String name, String declared, List<String> path, int pos) {
    public boolean inferred() { return declared == null; }
    @Override public String toString() { return "def " + name + (declared != null ? ": " + declared : "") + (path != null ? " = " + String.join(".", path) : ""); }
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
    private static final Pattern TOKEN = Pattern.compile("\\s+|//[^\\n]*|([A-Za-z_][A-Za-z0-9_]*|[(){}:=.,])");
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

    private Set<String> mods() {
      Set<String> mods = new LinkedHashSet<>();
      while (peek() != null && Set.of("case", "implicit", "nowarn", "deprecated").contains(peek())) mods.add(next());
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
      List<String> path = new ArrayList<>();
      path.add(ident());
      while (accept(".")) path.add(ident());
      return new Member(mods, name, declared, List.copyOf(path), pos);
    }
  }
}
