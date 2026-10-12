import VersoManual
import Jvm.Catalogue

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Overriding" =>
%%%
shortTitle := "Overriding"
htmlSplit := .never
%%%

Java and the JVM each define overriding, at different times and over different things.
The JLS defines it over source signatures, for javac to check a class.
The JVMS defines it over names and descriptors, for `invokevirtual` to choose the method to run.
On the rule that decides most binary-compatibility questions, package access, they agree.

# The two definitions

> An instance method mC declared in or inherited by class C, overrides from C another method mA declared in class A, iff all of the following are true:

  * C is a subclass of A.
  * C does not inherit mA.
  * The signature of mC is a subsignature (§8.4.2) of the signature of mA as a member of the supertype of C that names A.
  * One of the following is true:
    - mA is public.
    - mA is protected.
    - mA is declared with package access in the same package as C, and either C declares mC or mA is a member of the direct superclass type of C.

— [JLS §8.4.8.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-8.html#jls-8.4.8.1), Java SE 21. Two further cases, not quoted, let a package-access method be overridden transitively through a superclass.

> An instance method mC can override another instance method mA iff all of the following are true:

  * mC has the same name and descriptor as mA.
  * mC is not marked `ACC_PRIVATE`.
  * One of the following is true:
    - mA is marked `ACC_PUBLIC`.
    - mA is marked `ACC_PROTECTED`.
    - mA is marked neither `ACC_PUBLIC` nor `ACC_PROTECTED` nor `ACC_PRIVATE`, and either (a) the declaration of mA appears in the same run-time package as the declaration of mC, or (b) if mA is declared in a class A and mC is declared in a class C, then there exists a method mB declared in a class B such that C is a subclass of B and B is a subclass of A and mC can override mB and mB can override mA.

— [JVMS §5.4.5](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-5.html#jvms-5.4.5), Java SE 21.

The JLS compares signatures after substitution, the JVMS compares erased descriptors.
Where they differ, for example an override that narrows a generic method's parameter type, javac
emits a bridge method so that the JVM's relation holds as well.
The model of the JVM states §5.4.5 without the transitive case (b):

{docstring Jvm.overrides}

# Selection

The JVMS uses "can override" when `invokevirtual` picks the method to run for the receiver's
class C and the resolved method mR:

> If mR is marked `ACC_PRIVATE`, then it is the selected method.

  Otherwise, the selected method is determined by the following lookup procedure:

  * If C contains a declaration of an instance method m that can override mR (§5.4.5), then m is the selected method.
  * Otherwise, if C has a superclass, a search for a declaration of an instance method that can override mR is performed, starting with the direct superclass of C and continuing with the direct superclass of that class, and so forth, until a method is found or no further superclasses exist. If a method is found, it is the selected method.

— [JVMS §5.4.6](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-5.html#jvms-5.4.6), Java SE 21. A third step, not quoted, falls back to the maximally specific superinterface methods.

{docstring Jvm.select}

# An override cut by package

A library class `A` in package 1 has a public method `m`.
A client class `X` in another package extends `A` and overrides `m`, and a class `B` in package 1
calls `m` on an `X`.
The library then makes `A.m` package-private.
This is a case of the model's catalogue of library edits, restated here and checked to be the same:

```lean
open Jvm Jvm.Catalogue Jvm.Site

/-- `A.m` becomes package-private. -/
def cut : Case where
  name := "overrideCutByPackage"
  mima := some "InaccessibleMethodProblem"
  v0 := [(.A, { header := p1,
                methods := [(.m, .v, inst)] })]
  v1 := [(.A, { header := p1,
                methods := [(.m, .v,
                  { access := .pkg })] })]
  client := [
    (.X, { header := { super := some .A },
           methods := [(.m, .v, inst)] }),
    (.B, { header := p1 })]
  prog := { sites :=
    [within .B (invokevirtual .A .m .v .X)] }

example : cut = overrideCutByPackage := rfl
```

Before the edit the call runs `X.m`; after it, `A.m`:

```lean (name := cutEval)
#eval (cut.before, cut.after)
```
```leanOutput cutEval
(Except.ok [Jvm.Catalogue.C.X], Except.ok [Jvm.Catalogue.C.A])
```

```lean
example : cut.before = .ok [.X] ∧
    cut.after = .ok [.A] := by decide
```

Everything still links, and different code runs.
The JLS agrees: recompiled against the new library, `X.m` is a method of its own that overrides
nothing, and javac reports no error.
MiMa reports the edit as an `InaccessibleMethodProblem` on `A.m`.
