import VersoManual
import Literate.Cases

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Constructors" =>
%%%
shortTitle := "Constructors"
htmlSplit := .never
%%%

A client's `new A(0)` compiles to `new A`, `dup` and `invokespecial A.<init>(I)V`. The constructor
reference resolves like a method reference, through the superclasses, but constructors are not
inherited, so `invokespecial` adds a check after resolution:

> Otherwise, if the resolved method is an instance initialization method, and the class in which it is declared is not the class symbolically referenced by the instruction, a NoSuchMethodError is thrown.

— [JVMS §6.5 invokespecial](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-6.html#jvms-6.5.invokespecial), linking exceptions, Java SE 21.

# Removing a constructor

The JLS treats deleting a constructor and deleting a method together:

> Deleting a method or constructor from a class may break compatibility with any pre-existing binary that referenced this method or constructor; a NoSuchMethodError may be thrown when such a reference from a pre-existing binary is linked. Such an error will occur only if no method with a matching signature and return type is declared in a superclass.

— [JLS §13.4.12](https://docs.oracle.com/javase/specs/jls/se21/html/jls-13.html#jls-13.4.12), Java SE 21.

The last sentence holds for methods, where a superclass's declaration is found and runs. For a
constructor it gives no protection: moving `B(int)` up to `A` leaves a matching declaration in a
superclass, and the old client's `new B(0)` still fails, by the `invokespecial` rule above
(`ctorPulledUp`).
The order of the two checks matters too. Resolution's access check comes first, so when the
constructor moves up and becomes private there the error is `IllegalAccessError`, not
`NoSuchMethodError` (`ctorPulledUpPrivate`). Both were checked on HotSpot 21, 25 and 27.

# The cases

```lean
open Jvm.Catalogue

def ctors : List Case :=
  [ctorRemoved, ctorBecomesPrivate,
   ctorBecomesPackagePrivate, ctorPulledUp,
   ctorPulledUpPrivate, ctorClassBecomesAbstract]
```

```lean (name := ctorsEval)
#eval for k in ctors do
  IO.println (Literate.caseRow k)
```
```leanOutput ctorsEval
ctorRemoved: runs A → noSuchMethod (DirectMissingMethodProblem)
ctorBecomesPrivate: runs A → illegalAccess (DirectMissingMethodProblem)
ctorBecomesPackagePrivate: runs A → illegalAccess (InaccessibleMethodProblem)
ctorPulledUp: runs B → noSuchMethod (DirectMissingMethodProblem)
ctorPulledUpPrivate: runs B → illegalAccess (DirectMissingMethodProblem)
ctorClassBecomesAbstract: runs A → instantiation (AbstractClassProblem)
```

MiMa reports every one, but not always as the error the client gets: a constructor made private,
in place or after moving up, is a `DirectMissingMethodProblem`, and the client fails with
`IllegalAccessError`.

# The default constructor

> If the source code for a non-inner class contains no declared constructors, then a default constructor with no parameters is implicitly declared (§8.8.9). Adding one or more constructor declarations to the source code of such a class will prevent this default constructor from being implicitly declared, effectively deleting a constructor, unless one of the new constructors also has no parameters, thus replacing the default constructor.

— [JLS §13.4.12](https://docs.oracle.com/javase/specs/jls/se21/html/jls-13.html#jls-13.4.12), Java SE 21.

The model works on classfiles, where the default constructor is an ordinary `<init>()V`, so this
edit is `ctorRemoved` with the descriptor `()V`. Its source-level side is a gap in the Java
model: its lowering synthesizes the default constructor, with the class's access as the JLS goes on
to require, but its syntax has no constructor declarations, so the edit that adds one and removes
the default cannot be written yet.
