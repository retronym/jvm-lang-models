import VersoManual
import Jvm.Catalogue

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Linking" =>
%%%
shortTitle := "Linking"
htmlSplit := .never
%%%

A client's classfile names the members it uses symbolically: a class, a name, a descriptor.
The JVM turns each reference into an actual member when the client first uses it.
That step is _resolution_, and its rules decide whether a client compiled against one version
of a library still runs against the next.
The model in `Jvm.Link` states those rules as a {name}`Query.Task` over the class table, so the
answers a client's linkage reads are a trace, and an edit that leaves the trace's answers alone
cannot change how the client links ({name}`Jvm.link_congr`).

# Field resolution

The JVMS states the search order for a field in four steps:

> If C declares a field with the name and descriptor specified by the field reference, field lookup succeeds. The declared field is the result of the field lookup.
>
> Otherwise, field lookup is applied recursively to the direct superinterfaces of the specified class or interface C.
>
> Otherwise, if C has a superclass S, field lookup is applied recursively to S.
>
> Otherwise, field lookup fails.

— [JVMS §5.4.3.2](https://docs.oracle.com/javase/specs/jvms/se21/html/jvms-5.html#jvms-5.4.3.2), Java SE 21.

The sentence before the steps says that resolution "first attempts to look up the referenced field
in C and its superclasses", but the steps themselves try the superinterfaces *before* the
superclass. The model follows the steps:

{docstring Jvm.lookupField}

The order matters when a library changes.
Take a class `A` with an instance field `m`, an interface `I`, and a class `B` that extends `A` and
implements `I`.
A client compiled against this library reads `new B().m`, which javac emits as a reference to
`B.m`, and it resolves to `A`'s field.
Now the library gives `I` a field `m`. Interface fields are `static final`:

```lean
open Jvm Jvm.Catalogue

/-- The library after the edit: `I` has gained `m`. -/
def edited : W := world [
  (.A, { fields := [(.m, .s, {})] }),
  (.I, { header := { isInterface := true },
         fields := [(.m, .s,
           { isStatic := true, isFinal := true })] }),
  (.B, { header :=
           { super := some .A, ifaces := [.I] } })]

/-- Where lookup for `B.m` lands, run on `edited`. -/
def owner : Option C :=
  let r := (lookupField (C := C) .m .s depth .B).run
  match Query.Task.run (answer edited) r with
  | .ok (some (c, _)) => some c
  | _ => none
```

The lookup now stops at the interface, before it reaches the superclass:

```lean (name := ownerEval)
#eval owner
```
```leanOutput ownerEval
some (Jvm.Catalogue.C.I)
```

and the kernel checks the same fact:

```lean
example : owner = some .I := by decide
```

The client's `getfield B.m` now resolves to a static field, and HotSpot raises
`IncompatibleClassChangeError: Expected non-static field`.
MiMa 1.2.1 reports nothing for this edit: its field check looks in a class and its superclasses
only. Reported as [scala-garden/mima#995](https://github.com/scala-garden/mima/issues/995), with a
Java reproducer checked on HotSpot 21.
