# JBS submission: JVMS §5.3.5 loading-check order

The text for [bugreport.java.com](https://bugreport.java.com/bugreport/), as entered on 13 October 2026. The submission failed with the site's "Unexpected outage" page (reference error `0.4ca82d17.1791844236.33a0747`); resubmit when the form works, then replace this file with a link to the JBS issue. Background: [`jvms-derivation-check-order.md`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/docs/upstream/jvms-derivation-check-order.md).

**Synopsis.** When a class has a inaccessible super class and names a class as an interface, the latter error is reported, JVMS §5.3.5 say accessibility error is checked first

**Operating system.** Generic. **Java version.** 27. **Frequency.** Always.

**Description.**

X extends p1.A, where p1.A is final and package-private, X in another package: §5.3.5 gives IllegalAccessError (the superclass's resolution fails its access check); HotSpot throws IncompatibleClassChangeError: class X cannot inherit from final class p1.A

X extends p1.A implements B, where p1.A is package-private and B is a class: §5.3.5 gives IllegalAccessError; HotSpot throws IncompatibleClassChangeError: class X can not implement B, because it is not an interface

Note these changes require separate compilation, javac rejects the program if jointly compiled.

Is the step order of §5.3.5 normative? If it is, HotSpot does not conform; if not, the JVMS could say that the order of these checks is unspecified, as it does for when resolution happens (§5.4).

**Steps to reproduce.** The script in [`jvms-derivation-check-order.md`](https://github.com/retronym/jvm-lang-models/blob/a24eb574fc/docs/upstream/jvms-derivation-check-order.md#steps-to-reproduce), run as `./repro.sh $JDK_HOME`.

**Expected result.**

```
X1: java.lang.IllegalAccessError: class X1 cannot access its superclass p1.A (X1 and p1.A are in unnamed module of loader 'app')
X2: java.lang.IllegalAccessError: class X2 cannot access its superclass p1.A (X2 and p1.A are in unnamed module of loader 'app')
X3: java.lang.IllegalAccessError: class X3 cannot access its superclass p1.C (X3 and p1.C are in unnamed module of loader 'app')
```

**Actual result.**

```
X1: java.lang.IncompatibleClassChangeError: class X1 cannot inherit from final class p1.A
X2: java.lang.IncompatibleClassChangeError: class X2 can not implement B, because it is not an interface (B is in unnamed module of loader 'app')
X3: java.lang.IllegalAccessError: class X3 cannot access its superclass p1.C (X3 and p1.C are in unnamed module of loader 'app')
```

**Workaround.** None needed; this is a minor spec inconsistency with the implementation.
