import VersoManual
import Literate.Cases

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Sealed classes" =>
%%%
shortTitle := "Sealed classes"
htmlSplit := .never
%%%

A sealed class lists its permitted direct subclasses in the `PermittedSubclasses` attribute, and
the JVM enforces the list when it loads a subclass. Sealing a class that clients extend is a
breaking change:

> If a class that was freely extensible (§8.1.1.2) is changed to be declared sealed, then an IncompatibleClassChangeError is thrown if a binary of a pre-existing subclass of this class is loaded and is not a permitted direct subclass of this class (§8.1.6); such a change is not recommended for widely distributed classes.

  Adding a class to the set of permitted direct subclasses of a sealed class will not break compatibility with pre-existing binaries.

— [JLS §13.4.2.1](https://docs.oracle.com/javase/specs/jls/se21/html/jls-13.html#jls-13.4.2.1), Java SE 21.

# Loading a subclass

The JVMS states the check as part of deriving a class, after the check that the superclass is not
final:

> Otherwise, if the class named as the direct superclass of C has a PermittedSubclasses attribute (§4.7.31) and any of the following is true, derivation throws an IncompatibleClassChangeError:

  * The superclass is in a different run-time module than C (§5.3.6).
  * C does not have its `ACC_PUBLIC` flag set (§4.1) and the superclass is in a different run-time package than C (§5.3).
  * No entry in the classes array of the superclass's PermittedSubclasses attribute refers to a class or interface with the name N.

— [JVMS §5.3.5](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-5.html#jvms-5.3.5), Java SE 21.

The model has a single module, so the first condition never holds:

{docstring Jvm.permits}

{docstring Jvm.loadK}

# The cases

```lean
open Jvm.Catalogue

def sealing : List Case :=
  [classBecomesSealed, classBecomesSealedPermitting,
   ifaceBecomesSealed,
   sealedPermitsNonPublicElsewhere,
   sealedPermitsPublicElsewhere]
```

```lean (name := sealingEval)
#eval for k in sealing do
  IO.println (Literate.caseRow' k)
```
```leanOutput sealingEval
classBecomesSealed: loads → incompatibleClassChange
classBecomesSealedPermitting: loads → loads
ifaceBecomesSealed: loads → incompatibleClassChange
sealedPermitsNonPublicElsewhere: loads → incompatibleClassChange
sealedPermitsPublicElsewhere: loads → loads
```

The JLS clause covers the first two. The third is the same for an interface: the JVMS applies the
same three conditions to each direct superinterface.
The last two are the package condition: a sealed class in package 1 permits the client's
subclass by name, but the subclass is in another package, so it must be public.

On HotSpot the error is `IncompatibleClassChangeError`, "cannot inherit from sealed class". HotSpot's
class file parser checks `PermittedSubclasses` after the final-superclass check and before the
superclass's access check, and the model loads a class in the same order.
