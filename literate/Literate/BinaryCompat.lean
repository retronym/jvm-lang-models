import VersoManual
import Jvm.Catalogue

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Binary compatibility" =>
%%%
shortTitle := "Binary compatibility"
htmlSplit := .never
%%%

Chapter 13 of the JLS lists which changes to a library keep pre-existing binaries working.
It argues each claim in prose, from the JVM's linking rules.
The model's catalogue of library edits states the same claims as cases: a library before and after
an edit, a client compiled against the first, and what linking the client does with each.
Each case is checked by the kernel, and was run on HotSpot 21, 25 and 27, which gave the result the
model predicts except where JDK 21 has a known bug (Track J in `packages/jvm/docs/track-j.md`).

# Final methods

> Changing an instance method that is not declared final to be declared final may break compatibility with existing binaries that depend on the ability to override the method.

  If Super is recompiled but not Test, then running the new binary with the existing binary of Test results in an IncompatibleClassChangeError because the class Test improperly tries to override the instance method out.

— [JLS §13.4.17](https://docs.oracle.com/javase/specs/jls/se21/html/jls-13.html#jls-13.4.17), Java SE 21.

The JVM checks this when it loads the overriding class, before any method runs:

{docstring Jvm.loadK}

```lean
open Jvm Jvm.Catalogue Jvm.Site

/-- `A.m` becomes final; the client's `X`
overrides it. -/
def madeFinal : Case where
  name := "methodBecomesFinal"
  mima := some "FinalMethodProblem"
  v0 := [(.A, { methods := [(.m, .v, inst)] })]
  v1 := [(.A, { methods :=
           [(.m, .v, { isFinal := true })] })]
  client := [(.X, { header := { super := some .A },
                    methods := [(.m, .v, inst)] })]
  prog := { loads := [.X] }

example : madeFinal = methodBecomesFinal := rfl
```

```lean (name := finalEval)
#eval (madeFinal.before, madeFinal.after)
```
```leanOutput finalEval
(Except.ok [], Except.error (Jvm.LinkError.finalOverride))
```

HotSpot reports `finalOverride` as an `IncompatibleClassChangeError`, as the JLS says.

# Static methods

> If a method that is not declared private is also declared static (that is, a class method) and is changed to not be declared static (that is, to an instance method), or vice versa, then compatibility with pre-existing binaries may be broken, resulting in a linkage time error, namely an IncompatibleClassChangeError, if these methods are used by the pre-existing binaries.

— [JLS §13.4.19](https://docs.oracle.com/javase/specs/jls/se21/html/jls-13.html#jls-13.4.19), Java SE 21.

```lean
example : becomesStatic.before = .ok [.A] ∧
    becomesStatic.after =
      .error .incompatibleClassChange := by
  decide
```

# Adding a field

> Adding a field to a class may break compatibility with pre-existing binaries that are not recompiled. Assume a reference to a field f with qualifying class C. Assume further that f is in fact an instance (respectively static) field declared in a superclass of C, S, and that the type of f is X. If a new field of type X with the same name as f is added to a subclass of S that is a superclass of C or C itself, then a linkage error may occur. Such a linkage error will occur only if, in addition to the above, either one of the following is true:

  * The new field is less accessible than the old one.
  * The new field is a static (respectively instance) field.

— [JLS §13.4.8](https://docs.oracle.com/javase/specs/jls/se21/html/jls-13.html#jls-13.4.8), Java SE 21.

The clause says when the edit is an error. It does not say what happens otherwise: the reference
links, to the new field. A client compiled against `A` and `B extends A` reads `B.m`, which
resolves to `A`'s field; the library then gives `B` a field `m` of the same type:

```lean (name := shadowEval)
#eval (fieldShadowed.before, fieldShadowed.after)
```
```leanOutput shadowEval
(Except.ok [Jvm.Catalogue.C.A], Except.ok [Jvm.Catalogue.C.B])
```

The client reads a different field, with no error. When the new field is static and in a
superinterface, field resolution finds it before the superclass's field, and the read fails with
`IncompatibleClassChangeError`, the second case above. MiMa 1.2.1 misses that edit
([scala-garden/mima#995](https://github.com/scala-garden/mima/issues/995)); the Linking page works
through it.

# The catalogue

Every case of the first group, with what the client does before and after the edit and the problem
MiMa reports for it, computed from the model:

```lean
/-- The last component of a constructor's name. -/
def short {α} [Repr α] (a : α) : String :=
  ((reprStr a).splitOn ".").getLast!

def fmt : Except LinkError (List C) → String
  | .ok [] => "loads"
  | .ok cs =>
    "runs " ++ ", ".intercalate (cs.map short)
  | .error e => short e

def caseRow (k : Case) : String :=
  s!"{k.name}: {fmt k.before} → {fmt k.after}" ++
    match k.mima with
    | some p => s!" ({p})"
    | none => " (MiMa: nothing)"
```

```lean (name := table)
#eval for k in all do IO.println (caseRow k)
```
```leanOutput table
methodRemoved: runs A → noSuchMethod (DirectMissingMethodProblem)
resultTypeChanged: runs A → noSuchMethod (IncompatibleResultTypeProblem)
classBecomesInterface: runs A → incompatibleClassChange (IncompatibleTemplateDefProblem)
becomesStatic: runs A → incompatibleClassChange (VirtualStaticMemberProblem)
becomesAbstract: runs A → instantiation (AbstractClassProblem)
becomesFinal: loads → finalSuper (FinalClassProblem)
methodBecomesFinal: loads → finalOverride (FinalMethodProblem)
superclassRemoved: runs A → noSuchMethod (MissingTypesProblem)
defaultRemoved: runs I → abstractMethod (DirectAbstractMethodProblem)
defaultConflict: runs I → incompatibleClassChange (MiMa: nothing)
overrideAdded: runs A → runs B (MiMa: nothing)
pulledUp: runs B → runs A (MiMa: nothing)
```

The two cases MiMa reports nothing for, `overrideAdded` and `pulledUp`, are compatible: the client
links and runs the method a recompiled client would.
`defaultConflict` is not, and is the subject of the next page.
