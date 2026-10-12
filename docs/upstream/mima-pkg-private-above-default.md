# Draft: scala-garden/mima issue

**Tracker search (13 October 2026).** None found. I searched scala-garden/mima for package-private, IllegalAccessError and default method. [#994](https://github.com/scala-garden/mima/issues/994) (a member a subclass adds) is the nearest, but there the new member is in the class the client references, and its access or `static` is the problem. Here the new member is in a superclass the client never names, and the problem is selection. [#961](https://github.com/scala-garden/mima/issues/961) and [#301](https://github.com/scala-garden/mima/issues/301) concern defaults, but are false positives. On the JVM side, the behaviour is the specification: a superclass method beats an interface default in selection, and `invokeinterface` then requires it to be public or private.

**Title:** A package-private method added to a class can break `invokeinterface` on a subclass that inherits a default, and is not reported

A class that gains a package-private (or protected) method can break a client's call through an interface, when the client's own class extends the class and inherits a default method of the same name and descriptor. `invokeinterface` selects the class's method, which is neither public nor private, and throws `IllegalAccessError` (JVMS §6.5). MiMa reports nothing.

```java
package p;
public interface I { default int m() { return 1; } }   // unchanged

// v1
package p;
public class A {}

// v2
package p;
public class A { int m() { return 2; } }   // or: protected int m()
```

A client compiled against v1:

```java
public class Client {
  static class X extends p.A implements p.I {}
  public static void main(String[] args) {
    p.I i = new X();
    System.out.println(i.m());
  }
}
```

prints `1` against v1. Against v2, on HotSpot 21, 25 and 27:

```
java.lang.IllegalAccessError: 'int Client$X.m()'
```

`A` does not implement `I`, so javac accepts v2. With the package-private form it even accepts `Client` recompiled against v2: `A.m` is not inherited outside `p`, so `X.m` is `I.m` (JLS §8.4.8). The recompiled client throws the same error. JVM selection (JVMS §5.4.6) searches `X`'s superclasses first, and `A.m` "can override" the public `I.m` (§5.4.5), so it is selected. Then:

> Otherwise, if the selected method is neither public nor private, invokeinterface throws an IllegalAccessError.

([JVMS §6.5 invokeinterface](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-6.html#jvms-6.5.invokeinterface), run-time exceptions). With `protected int m()`, a recompile fails ("m() in A cannot implement m() in I"), and the old client throws the same `IllegalAccessError`.

MiMa 1.2.1 reports no problem for either v1 to v2: a new method is not a problem in itself, and a non-public one is not checked.

Suggested fix: report a non-public, non-private instance method added to a public, non-final class when a public interface method with the same name and descriptor could reach a subclass. Conservatively, that is any such method, since the client chooses the interface. Narrower: when the name and descriptor match a public method of an interface on the classpath. The rule belongs with the inherited-member checks of #994 and #995.

Found while checking MiMa's rules against a model of JVM linkage ([retronym/jvm-lang-models, `packages/mima`](https://github.com/retronym/jvm-lang-models/tree/main/packages/mima), catalogue case `pkgMethodAboveDefault`), with an LLM's help, and reproduced on HotSpot 21, 25 and 27 and MiMa 1.2.1. The model's corrected rules for #993 to #996 missed it too; they now report it (`subSelectsCheck`, scoped to the library's own interfaces).
