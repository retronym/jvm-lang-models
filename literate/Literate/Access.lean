import VersoManual
import Literate.Cases

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Access control" =>
%%%
shortTitle := "Access control"
htmlSplit := .never
%%%

The JVM checks access twice: when it resolves a reference, and, for protected members, when it
verifies the class that makes the reference. A library edit that narrows access can fail at either.

# At resolution

> A field or method R is accessible to a class or interface D if and only if any of the following is true:

  * R is public.
  * R is protected and is declared in a class C, and D is either a subclass of C or C itself. Furthermore, if R is not static, then the symbolic reference to R must contain a symbolic reference to a class T, such that T is either a subclass of D, a superclass of D, or D itself.
  * R is either protected or has default access (that is, neither public nor protected nor private), and is declared by a class in the same run-time package as D.
  * R is private and is declared by a class or interface C that belongs to the same nest as D, according to the nestmate test below.

  If R is not accessible to D, then access control throws an IllegalAccessError.

— [JVMS §5.4.4](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-5.html#jvms-5.4.4), Java SE 21.

The model leaves out nests: a private member is accessible from its own class only.

{docstring Jvm.accessible}

# At verification

Resolution's condition on a protected member is on the class `T` that the reference names. The
verifier adds one on the object the member is accessed through:

> The protected check applies only to protected members of superclasses of the current class. protected members in other classes will be caught by the access checking done at resolution (§5.4.4).

— [JVMS §4.10.1.8](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-4.html#jvms-4.10.1.8), Java SE 21.

{docstring Jvm.verifyProtected}

# Narrowing to protected

> Changing the declared access of a member or constructor to permit less access may break compatibility with pre-existing binaries, causing a linkage error to be thrown when these binaries are resolved.

— [JLS §13.4.7](https://docs.oracle.com/javase/specs/jls/se21/html/jls-13.html#jls-13.4.7), Java SE 21.

A library class `A` in package 1 makes a public method `m` protected. Three clients call it from
another package: an unrelated class calling `m` on an `A`; a subclass `X` calling `m` on itself;
and `X` calling `m` on an `A` that is not an `X`. The edit is the same in each; the outcomes are not:

```lean
open Jvm.Catalogue

def narrowed : List Case :=
  [methodBecomesProtected,
   methodBecomesProtectedSub,
   methodBecomesProtectedOther]
```

```lean (name := narrowedEval)
#eval for k in narrowed do
  IO.println (Literate.caseRow k)
```
```leanOutput narrowedEval
methodBecomesProtected: runs A → illegalAccess (InaccessibleMethodProblem)
methodBecomesProtectedSub: runs A → runs A (InaccessibleMethodProblem)
methodBecomesProtectedOther: runs A → verify (InaccessibleMethodProblem)
```

The unrelated class fails at resolution. The subclass calling `m` on itself still links.
The subclass calling `m` on another `A` passes resolution, since `X` is a subclass of `A` and the
reference names `A`, a superclass of `X`; the verifier then rejects `X` with a `VerifyError`
before any of its code runs. HotSpot 21, 25 and 27 agree on all three.

MiMa reports the same problem for each, including the client that still links: it judges the edit,
not a client.
