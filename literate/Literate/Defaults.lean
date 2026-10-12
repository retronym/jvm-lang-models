import VersoManual
import Jvm.Catalogue

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Default methods" =>
%%%
shortTitle := "Default methods"
htmlSplit := .never
%%%

A default method gives an interface an implementation, so the JVM can find the method a call runs
in a superinterface as well as in a superclass.
Resolution and selection both fall back to the superinterfaces through one definition:

> A maximally-specific superinterface method of a class or interface C for a particular method name and descriptor is any method for which all of the following are true:

  * The method is declared in a superinterface (direct or indirect) of C.
  * The method is declared with the specified name and descriptor.
  * The method has neither its `ACC_PRIVATE` flag nor its `ACC_STATIC` flag set.
  * Where the method is declared in interface I, there exists no other maximally-specific superinterface method of C with the specified name and descriptor that is declared in a subinterface of I.

— [JVMS §5.4.3.3](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-5.html#jvms-5.4.3.3), Java SE 21.

{docstring Jvm.maxSpecific}

When no class in the receiver's superclass chain declares the method, selection takes the unique
non-abstract maximally-specific method. If there is not exactly one, the call fails:

> Otherwise, if no method is selected, and there are multiple maximally-specific superinterface methods of C that match the resolved method's name and descriptor and are not abstract, invokeinterface throws an IncompatibleClassChangeError

  Otherwise, if no method is selected, and there are no maximally-specific superinterface methods of C that match the resolved method's name and descriptor and are not abstract, invokeinterface throws an AbstractMethodError.

— [JVMS §6.5 invokeinterface](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-6.html#jvms-6.5.invokeinterface), run-time exceptions, Java SE 21.

# Adding a default method

The JLS calls adding a default method binary compatible, with one exception:

> Adding a default method, or changing a method from abstract to default, does not break compatibility with pre-existing binaries, but may cause an IncompatibleClassChangeError if a pre-existing binary attempts to invoke the method. This error occurs if the qualifying interface of the method invocation, K, is a subinterface of two interfaces, I and J, where both I and J declare a default method with the same signature and result, and neither I nor J is a subinterface of the other.

— [JLS §13.5.7](https://docs.oracle.com/javase/specs/jls/se21/html/jls-13.html#jls-13.5.7), Java SE 21.

The JLS describes a conflict that resolution meets, on the interface the call names.
The same conflict can wait until selection. The client's class `X` implements `I` and `J`, and calls
`m` through `I`, which has a default. The library then gives `J` a default `m` too:

```lean
open Jvm Jvm.Catalogue Jvm.Site

def ifc (ms : List (N × D × MethodInfo C N D)) :
    Classfile C N D :=
  { header := { isInterface := true }, methods := ms }

/-- `J` gains a default `m`. -/
def clash : Case where
  name := "defaultConflict"
  mima := none
  v0 := [(.I, ifc [(.m, .v, inst)]), (.J, ifc [])]
  v1 := [(.I, ifc [(.m, .v, inst)]),
         (.J, ifc [(.m, .v, inst)])]
  client := [(.X, { header := { ifaces := [.I, .J] } })]
  prog := { loads := [.X],
            sites := [invokeinterface .I .m .v .X] }

example : clash = defaultConflict := rfl
```

```lean (name := clashEval)
#eval (clash.before, clash.after)
```
```leanOutput clashEval
(Except.ok [Jvm.Catalogue.C.I], Except.error (Jvm.LinkError.incompatibleClassChange))
```

Resolution of `I.m` finds `I`'s default, as before. Selection on `X` finds no class method, and two
maximally-specific defaults, so the call fails as the first quoted rule says.
MiMa reports nothing: the edit adds a method to `J` and changes nothing the client refers to.

On HotSpot 25 and 27 the call throws `IncompatibleClassChangeError`. HotSpot 21 throws
`AbstractMethodError` instead, the second rule's error: [JDK-8356942](https://bugs.openjdk.org/browse/JDK-8356942),
a regression since JDK 10, fixed in JDK 25. The probe hit it when it ran the catalogue on all three
JDKs.

The opposite edit, a default made abstract, is the second rule:

```lean
example : defaultRemoved.before = .ok [.I] ∧
    defaultRemoved.after =
      .error .abstractMethod := by
  decide
```
