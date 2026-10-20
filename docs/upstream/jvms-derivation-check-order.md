# HotSpot checks a class's superinterfaces and its superclass's finality before the superclass's access

Draft, not posted. Venue: OpenJDK JBS, component hotspot/runtime (or specification/vm if the JVMS is meant to leave the order open).

**JVMS 25 §5.3.5.** Deriving a class `C` resolves its direct superclass by §5.4.3.1 (step 3), whose last step is access control (§5.4.4); only then does it check that the superclass is not an interface, not final and permits `C`; and only then (step 4) does it resolve and check the direct superinterfaces. So when a class breaks two of these, the specification says which exception is thrown.

**HotSpot 21, 25 and 27** check in another order: the superinterfaces first, and the superclass's finality before its accessibility. Two classfiles, rendered with the Classfile API by [`packages/jvm/probes`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/packages/jvm/probes):

- `X extends p1.A`, where `p1.A` is final and package-private, `X` in another package: §5.3.5 gives `IllegalAccessError` (the superclass's resolution fails its access check); HotSpot throws `IncompatibleClassChangeError: class X cannot inherit from final class p1.A` ([`Catalogue.finalSuperInaccessible`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/packages/jvm/Jvm/Catalogue.lean#L677)).
- `X extends p1.A implements B`, where `p1.A` is package-private and `B` is a class: §5.3.5 gives `IllegalAccessError`; HotSpot throws `IncompatibleClassChangeError: class X can not implement B, because it is not an interface` ([`Catalogue.ifaceNotIfaceSuperInaccessible`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/packages/jvm/Jvm/Catalogue.lean#L689)).

Both are reached with javac alone, by recompiling the library after the client: `X1 extends p1.A` and `X2 extends p1.A implements B` are compiled against a public `p1.A` and an interface `B`; then `p1.A` becomes package-private and final, and `B` a class. `X3 extends p1.C`, where `p1.C` only becomes package-private, is the control: the access check exists and throws `IllegalAccessError` when it is the only failure.

## Steps to reproduce

Save as `repro.sh` and run `./repro.sh $JDK_HOME` in an empty directory:

```bash
#!/usr/bin/env bash
# JVMS §5.3.5 vs HotSpot: which LinkageError when a class's superclass is both inaccessible and final,
# or inaccessible while a superinterface is a class. Usage: ./repro.sh JDK_HOME
set -e
J=${1:?JDK home}/bin
rm -rf v1 v2 cls && mkdir -p v1/p1 v2/p1 cls
# v1: what the client is compiled against
cat > v1/p1/A.java <<'J'
package p1; public class A {}
J
cat > v1/p1/C.java <<'J'
package p1; public class C {}
J
cat > v1/B.java <<'J'
public interface B {}
J
cat > X1.java <<'J'
public class X1 extends p1.A {}
J
cat > X2.java <<'J'
public class X2 extends p1.A implements B {}
J
cat > X3.java <<'J'
public class X3 extends p1.C {}
J
cat > Main.java <<'J'
public class Main {
  public static void main(String[] a) {
    for (String n : a) {
      try { Class.forName(n); System.out.println(n + ": loaded"); }
      catch (Throwable t) { System.out.println(n + ": " + t); }
    }
  }
}
J
$J/javac -d cls v1/p1/A.java v1/p1/C.java v1/B.java X1.java X2.java X3.java Main.java
# v2: A becomes package-private and final; B becomes a class; C (the control) only package-private
cat > v2/p1/A.java <<'J'
package p1; final class A {}
J
cat > v2/p1/C.java <<'J'
package p1; class C {}
J
cat > v2/B.java <<'J'
public class B {}
J
$J/javac -d cls v2/p1/A.java v2/p1/C.java v2/B.java
$J/java -version 2>&1 | head -1
$J/java -cp cls Main X1 X2 X3
```

On Temurin 21.0.12, 25.0.4 and 27 it prints:

```
X1: java.lang.IncompatibleClassChangeError: class X1 cannot inherit from final class p1.A
X2: java.lang.IncompatibleClassChangeError: class X2 can not implement B, because it is not an interface (B is in unnamed module of loader 'app')
X3: java.lang.IllegalAccessError: class X3 cannot access its superclass p1.C (X3 and p1.C are in unnamed module of loader 'app')
```

By the step order of §5.3.5, `X1` and `X2` would throw `IllegalAccessError`, as `X3` does. The question for the report: is the step order of §5.3.5 normative? If it is, HotSpot does not conform; if not, the JVMS could say that the order of these checks is unspecified, as it does for when resolution happens (§5.4).

The model follows HotSpot ([`Jvm.loadK`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/packages/jvm/Jvm/Link.lean#L339)), and the [specification ledger](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/docs/specification-ledger.md) records the disagreement.
