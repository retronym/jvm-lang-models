# Track N: binary names. Design brief

13 October 2026, for review before code.

## Problem

Every tool in the repository trusts a classfile's names, and each trusts them differently. The JVM links by them. MiMa compares members by them and decides privacy from classfile flags, so a member scalac made public to reach it from an inner class is, to MiMa, public API. Zinc records the simple names a unit uses and hashes members by name, so a synthetic or expanded name must be charged to the right source member or invalidation misses it. The IDE and the migration guides describe the Scala 2 and Scala 3 encodings in prose.

The model lowers to names only where the probe forced it: trait setters (`p1$T$_setter_$v_$eq`), `$init$`, `MODULE$`, static forwarders, `$values`, nested objects and the `InnerClasses` attribute, calibrated on 1,348 programs per compiler. Everything else that the compilers do to names is absent: private name expansion, super accessors, outer fields, the flattening and numbering of local, anonymous and lambda classes, default-argument getters, value-class extension methods, lazy-val encodings, specialisation suffixes, Scala 3's `inline$` and `$proxy` members. These are exactly where a source-private or source-invisible edit becomes a binary one, so they are where binary compatibility, Zinc and the 2-to-3 migration have unmodelled behaviour.

Two specifications are involved and both leave gaps. JLS §13.1 defines binary names for top-level and member classes and says local and anonymous class names are implementation-specific. The SLS does not define binary names at all; they are the compilers' convention, different between 2.12, 2.13 and 3.

## What it is

A names layer in the Scala and Java lowerings. A binary name is a structure, not a string: the owner chain, the kind of definition (class, module class, member, setter, accessor, default getter, extension, lazy slot, lambda, local or anonymous class with its index), and whether it was expanded for access. One function `mangle : Dialect → Name → String` produces the string the compiler writes, and it is calibrated by the probe through the compile server on enumerated spaces of nestings, visibilities and accesses. The structured name is what the consumers reason about; the string is what the JVM links by.

## Key decisions

**Structure first, string last.** Zinc's `Names` model and MiMa's keys should be restated over the structured name, so that "the same source member" is a question about the structure, and "the same binary name" a question about `mangle`. That is what lets the model say when a source-private edit is binary-breaking (the structure changes, so the string changes, so the inner class's reference fails) and when a binary change is source-invisible (a renumbered local class).

**Calibrate the string, not the convention.** The compilers' rules are read from their sources for the model's first draft (`ExpandPrivate`, `Flatten`, `LambdaLift`, `Mixin` and `Fields` in scalac; `ExpandPrivate`, `Flatten`, `LambdaLift`, `Getters` and `LazyVals` in dotc) and then held against the probe on spaces, as the lowering was. The probe already parses classfiles and diffs members, so the only new work is the space generators and the comparison of `InnerClasses`, `NestHost`/`NestMembers` (Scala 3, javac 11+) and `invokedynamic` bootstrap names.

**Three consumers, one layer.** The JVM catalogue gains source edits whose only effect is a binary name (a private member renamed, a local class added before another, a lambda reordered, a member made `private[this]`), linked before and after and run on HotSpot. The MiMa model is checked on expanded and synthetic members: what MiMa 1.2.1 reports for them, and whether that is a gap, a false positive, or the right call. Zinc's name-hash keys are stated over structured names, which decides whether an expanded name used by a client is covered by the key for the source member.

**Scala 2 and 3 as one parameter**, as `Dialect` already is for lowering. The differences in expansion, lazy-val encoding, default getters and lambda naming are read where the probe finds them, so the result is a calibrated table of 2-versus-3 binary differences for the same source, which the migration guides state only in part.

**Java in the same layer.** `Outer$Inner`, `Outer$1Local`, `Outer$1`, `this$0`, the pre-nestmate `access$000` accessors and the numbering of local classes, calibrated on javac 17, 21 and 25 as Track V did. JLS §13.1's "implementation-specific" is the omission to record in the specification ledger, with javac's actual rule beside it.

## Out of scope

Specialisation beyond the suffix (its own semantics), macro-generated names, Scala 2 `-Ydelambdafy:inline` classes, module names in `module-info`, and the TASTy side of names (which is not a classfile concern).

## Steps

Progress: the class-and-object part of steps 1 and 3 is [`Scala.Names`](../Scala/Names.lean), calibrated on its own space ([track-s.md](track-s.md), "Binary names of classes and objects"); `Lower` is not yet restated over it.


1. The structured `Name` and `mangle` for Scala 2.12, 2.13 and 3 over what the lowering already emits, restated so the existing 1,348-program calibration is unchanged. One commit; the probe is the check.
2. Expansion and accessors: private members reached from inner classes and companions, super accessors, outer fields and parameters. A space of nestings and accesses, calibrated on all three compilers.
3. Flattening and numbering: local, anonymous and lambda classes, with their indices; the `InnerClasses` and nestmate attributes; `invokedynamic` names. Calibrated; JLS §13.1 tagged in the ledger.
4. Synthetic members: default getters, extension methods, lazy-val encodings per version, `inline$` and `$proxy`. Calibrated.
5. Java: member, local and anonymous class names, outer fields, pre-nestmate accessors, on javac 17, 21 and 25.
6. Consumers: catalogue cases for name-only edits run on HotSpot and through MiMa; the MiMa model's verdicts on expanded names classified; Zinc's `Names` keys over structured names, with the bug map's naming gaps re-examined.

Each step is a commit series with the lints green and a record in [`track-s.md`](track-s.md) (Scala) or [`track-java.md`](../../java/docs/track-java.md) (Java); the findings go to the specification ledger and to [`docs/upstream`](../../../docs/upstream) as drafts.

## Expected findings

A class of MiMa gaps or false positives on expanded and synthetic names; a calibrated statement of javac's local-class numbering where JLS §13.1 says nothing; a table of Scala 2-versus-3 binary-name differences for the same source; and, through Zinc's keys, whether used-name tracking covers expanded names (the bug map has naming rows with no instance).
