package compileserver;

import java.util.*;

/**
 * A minimal JSON reader and writer: objects, arrays, strings, numbers, booleans, null. A superset of
 * packages/jvm/probes/Json.java (which reads no numbers and only the escapes it needs), for the compile
 * server's requests.
 */
public final class Json {
  private final String s;
  private int i;

  private Json(String s) { this.s = s; }

  public static Object parse(String s) {
    Json j = new Json(s);
    Object v = j.value();
    j.ws();
    if (j.i != s.length()) throw new IllegalArgumentException("trailing input at " + j.i);
    return v;
  }

  private void ws() { while (i < s.length() && Character.isWhitespace(s.charAt(i))) i++; }

  private Object value() {
    ws();
    char c = s.charAt(i);
    switch (c) {
      case '{': {
        i++;
        Map<String, Object> m = new LinkedHashMap<>();
        ws();
        if (s.charAt(i) == '}') { i++; return m; }
        while (true) {
          ws();
          String k = string();
          ws(); expect(':');
          m.put(k, value());
          ws();
          if (s.charAt(i) == ',') { i++; continue; }
          expect('}');
          return m;
        }
      }
      case '[': {
        i++;
        List<Object> l = new ArrayList<>();
        ws();
        if (s.charAt(i) == ']') { i++; return l; }
        while (true) {
          l.add(value());
          ws();
          if (s.charAt(i) == ',') { i++; continue; }
          expect(']');
          return l;
        }
      }
      case '"': return string();
      default:
        if (s.startsWith("true", i)) { i += 4; return Boolean.TRUE; }
        if (s.startsWith("false", i)) { i += 5; return Boolean.FALSE; }
        if (s.startsWith("null", i)) { i += 4; return null; }
        if (c == '-' || (c >= '0' && c <= '9')) return number();
        throw new IllegalArgumentException("unexpected '" + c + "' at " + i);
    }
  }

  private Object number() {
    int start = i;
    while (i < s.length() && "+-0123456789.eE".indexOf(s.charAt(i)) >= 0) i++;
    String t = s.substring(start, i);
    if (t.contains(".") || t.contains("e") || t.contains("E")) return Double.parseDouble(t);
    return Long.parseLong(t);
  }

  private void expect(char c) {
    if (s.charAt(i) != c) throw new IllegalArgumentException("expected '" + c + "' at " + i);
    i++;
  }

  private String string() {
    expect('"');
    StringBuilder b = new StringBuilder();
    while (s.charAt(i) != '"') {
      char c = s.charAt(i++);
      if (c != '\\') { b.append(c); continue; }
      char e = s.charAt(i++);
      switch (e) {
        case 'n': b.append('\n'); break;
        case 't': b.append('\t'); break;
        case 'r': b.append('\r'); break;
        case 'b': b.append('\b'); break;
        case 'f': b.append('\f'); break;
        case 'u': b.append((char) Integer.parseInt(s.substring(i, i + 4), 16)); i += 4; break;
        default: b.append(e);
      }
    }
    i++;
    return b.toString();
  }

  /** One line of JSON: no raw newlines, so a response is one line. */
  public static String write(Object o) {
    StringBuilder b = new StringBuilder();
    write(b, o);
    return b.toString();
  }

  private static void write(StringBuilder b, Object o) {
    if (o == null) b.append("null");
    else if (o instanceof String) quote(b, (String) o);
    else if (o instanceof Number || o instanceof Boolean) b.append(o);
    else if (o instanceof Map) {
      b.append('{');
      boolean first = true;
      for (Map.Entry<?, ?> e : ((Map<?, ?>) o).entrySet()) {
        if (!first) b.append(',');
        first = false;
        quote(b, String.valueOf(e.getKey()));
        b.append(':');
        write(b, e.getValue());
      }
      b.append('}');
    } else if (o instanceof Collection) {
      b.append('[');
      boolean first = true;
      for (Object x : (Collection<?>) o) {
        if (!first) b.append(',');
        first = false;
        write(b, x);
      }
      b.append(']');
    } else quote(b, o.toString());
  }

  private static void quote(StringBuilder b, String s) {
    b.append('"');
    for (int k = 0; k < s.length(); k++) {
      char c = s.charAt(k);
      switch (c) {
        case '"': b.append("\\\""); break;
        case '\\': b.append("\\\\"); break;
        case '\n': b.append("\\n"); break;
        case '\r': b.append("\\r"); break;
        case '\t': b.append("\\t"); break;
        default:
          if (c < 0x20) b.append(String.format("\\u%04x", (int) c));
          else b.append(c);
      }
    }
    b.append('"');
  }

  @SuppressWarnings("unchecked")
  public static Map<String, Object> obj(Object o) { return (Map<String, Object>) o; }

  @SuppressWarnings("unchecked")
  public static List<Object> arr(Object o) { return (List<Object>) o; }

  public static List<String> strings(Object o) {
    List<String> r = new ArrayList<>();
    if (o != null) for (Object x : arr(o)) r.add((String) x);
    return r;
  }
}
