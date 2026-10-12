# Track J — JVM linkage (`Jvm/`)

## Problem

Zinc asks whether a client must be *recompiled*; binary compatibility asks whether its old classfile still *links*, and runs the same code, against an edited library. Both are questions about a task's trace against an edited environment. The Zinc toys model erasure and forwarders inside each feature file, but nothing modelled linkage itself, so there was no ground truth to check MiMa against (Track B) and nothing for the Scala and Java front ends (Tracks S and V) to lower to.

## What was built

- **[`packages/jvm/Jvm/Link.lean`](../Jvm/Link.lean).** Linking as a `Task` over the class table: loading checks, resolution (JVMS §5.4.3.2–4), selection (§5.4.6) and access (§5.4.4, plus the verifier's receiver, `invokespecial` and protected rules). Its trace is the client's *linkage footprint*, so T1 applies unchanged: [`link_congr`](../Jvm/Link.lean#L662). `Compatible` and [`compatible_of_footprint`](../Jvm/Link.lean#L681) state binary compatibility and prove it where the edit misses the footprint.
- **The contract.** [`Jvm.World`](../Jvm/Link.lean#L108) (classfiles), [`Jvm.Program`](../Jvm/Link.lean#L641) (what a client loads and executes) and [`Jvm.Site`](../Jvm/Link.lean#L58). Front ends produce a `World`; consumers read one. These types were changed only additively.
- **Sites as javac emits them.** `C c = new R(); c.m()` is `new R; invokespecial R.<init>; invokevirtual C.m`, so the verifier's upcast check, instantiation and load-on-reference are part of `Site` semantics. `Site.construct c n d` is `new c(…)`.
- **[`packages/jvm/Jvm/Catalogue.lean`](../Jvm/Catalogue.lean).** Library edits, each with MiMa's expected problem, linked before and after by kernel `decide`.
- **[`packages/jvm/Jvm/Clients.lean`](../Jvm/Clients.lean).** `breaksSomeClient k`: some client in a bounded space links on `v0` and fails on `v1`. `changesSomeClient k`: some client links on both and runs a different method (the first form of "links, but runs different code"). Clients must be well-typed against `v0`. Three spaces: `space` (an optional client class `X` and one call site of any kind), `space3` (adds fields, `invokespecial`, interface statics, sites inside `X`), `space5` (constructors and `new`). Their sizes, and the catalogue's, are generated into [`docs/stats.md`](../../../docs/stats.md#jvm-catalogue-and-client-spaces).
- **The HotSpot probe.** `lake exe jvmcases` dumps the catalogue and spaces as JSON lines; [`packages/jvm/probes`](../probes) renders each case's `v0`, `v1` and client with the Classfile API (version 65), runs the client against both, and compares the `Throwable` and the method that ran. `OUT=dir` keeps the classfiles for MiMa.
- **No `native_decide`** (review finding 7). Catalogue witnesses use `decide`; client-space verdicts use `decide +kernel`, since the elaborator's `decide` hits its recursion limit.

Steps:
- Track J1: calibrate the catalogue on HotSpot. Done.
- Track J2: client spaces and verdicts. Done.
- Track J3: fields, `invokespecial`, private methods, static and private interface methods, access control, the protected check. Done, except nestmates and the smaller items in [`docs/roadmap.md`](../../../docs/roadmap.md).
- Track J5: sealed classes (`PermittedSubclasses`) and constructor calls. Done.
- Track J6: overriding along a chain of library classes, the shape of JVMS §5.4.5's example: `chainSpace` in [`Clients.lean`](../Jvm/Clients.lean) (`lake exe jvmcases chain`). Done; it found two model bugs, below.
- Clients in the library's package and a space over two client classes: done by `chainSpace` (client class `J` in package 0, 1 or 2 beside `X`); the catalogue's spaces still have one client class, in the unnamed package.
- Tracks J7 (default methods along superinterface chains) and J8 (field resolution through superinterfaces at depth): open, see [`docs/roadmap.md`](../../../docs/roadmap.md).
- Track J4: behaviour (constants, method bodies). Open, see [`docs/roadmap.md`](../../../docs/roadmap.md).

## Results

**Calibration.** On Temurin 21.0.12, 25.0.4 and 27, the probe agrees with the model on every catalogue case and on every program of `space`, `space3`, `space5` and `chainSpace`, apart from two known HotSpot bugs on JDK 21, below. Runs from Track J6 on are recorded in the [calibration ledger](../probes/runs/README.md), one line per run with its commit.

**[`LinkError`](../Jvm/Link.lean#L148) to the JVM's exceptions**, the same on all three JDKs: `noClassDef` → `NoClassDefFoundError`, `incompatibleClassChange` → `IncompatibleClassChangeError`, `noSuchMethod` → `NoSuchMethodError`, `noSuchField` → `NoSuchFieldError`, `abstractMethod` → `AbstractMethodError`, `instantiation` → `InstantiationError`, `illegalAccess` → `IllegalAccessError`, `verify` → `VerifyError`. `finalSuper` and `finalOverride` are `IncompatibleClassChangeError`, not `VerifyError`.

**What calibration added to the model.** Each of these was a disagreement first, and is now a rule:
- Loading a class checks that its superclass and superinterfaces are accessible (`IllegalAccessError`).
- The verifier's `invokespecial` rule turns on whether the referenced class is an interface, not on the constant's tag. An `InterfaceMethodref` to a class passes the verifier and fails resolution with ICCE; a reference to an interface that is not a direct superinterface is a `VerifyError`.
- The protected-receiver check (§4.10.1.8), predicted by `methodBecomesProtectedOther`.
- `PermittedSubclasses` (JVMS §5.3.5) is checked after the final-superclass check and before the access check, as HotSpot's class file parser does: the class must be listed and, unless public, in the sealed type's run-time package.
- A constructor resolves like any method, walking superclasses with an access check, and must then be declared by `c` itself (JVMS §6.5 `invokespecial`, linking exceptions), so an inherited match is `noSuchMethod` (`ctorPulledUp`). The access check comes first: an inherited private match is `illegalAccess` (`ctorPulledUpPrivate`).
- The final-method check at loading (§5.3.5) looks at every final method of every superclass, not the nearest declaration of the name. Found by Track J6: with a final `A.m` behind a `B.m` that does not override it (private, or package-private elsewhere), the model let `I` or `X` load, and HotSpot 21, 25 and 27 report "overrides final method A.m" (1,836 programs of the chain space). `methodBecomesFinalBehind` is the javac-reachable form, through a client in `A`'s package; MiMa 1.2.1 reports nothing for it, since `A.m` is package-private.
- Transitive overriding (§5.4.5 (b)): a package-private method is also overridden from another package through an intermediate method that overrides it and is overridden in turn. Found by encoding the JVMS's own example as `transitiveOverride`: the model, without (b), predicted `I.m` after the intermediate method became public, and HotSpot 21, 25 and 27 run `X.m`. The calibration spaces had not found it: no client of `space3` declares a package-private method in another package below two library classes.

**Known JDK bugs hit by the probe**, both fixed in JDK 25. The model follows the JVMS; the probe reports the JDK 21 results as known deviations.
- [JDK-8356942](https://bugs.openjdk.org/browse/JDK-8356942): `invokeinterface` on a receiver with two maximally-specific defaults throws `AbstractMethodError` instead of ICCE (`defaultConflict`). Regressed in JDK 10.
- [JDK-8350029](https://bugs.openjdk.org/browse/JDK-8350029): JDK 21's `invokespecial` verification checks the constant's tag, so it gives `VerifyError` where 25 gives ICCE, and the reverse. 56 programs of `space3` and 4 of `space5`, all in forms javac never emits.

**The catalogue on HotSpot.** "MiMa" is the first problem MiMa 1.2.1 reports (Track B). "HotSpot" is the result on `v1`; "same" means it links and runs the method the model predicts. Breaks and changes are counts over the clients that link on `v0`.

| Case | MiMa | Model on `v1` | HotSpot | Breaks some client | Changes some client |
|---|---|---|---|---|---|
| `methodRemoved` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (12/29) | no |
| `resultTypeChanged` | IncompatibleResultTypeProblem | `noSuchMethod` | `NoSuchMethodError` | yes (12/29) | no |
| `classBecomesInterface` | IncompatibleTemplateDefProblem | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (49/78) | no |
| `becomesStatic` | VirtualStaticMemberProblem | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (12/29) | no |
| `becomesAbstract` | AbstractClassProblem | `instantiation` | `InstantiationError` | yes (7/17) | no |
| `becomesFinal` | FinalClassProblem | `finalSuper` | `IncompatibleClassChangeError` | yes (8/17) | no |
| `methodBecomesFinal` | FinalMethodProblem | `finalOverride` | `IncompatibleClassChangeError` | yes (5/29) | no |
| `superclassRemoved` | MissingTypesProblem | `noSuchMethod` | `NoSuchMethodError` | yes (28/78) | no |
| `defaultRemoved` | DirectAbstractMethodProblem | `abstractMethod` | `AbstractMethodError` | yes (4/15) | no |
| `defaultConflict` | — | `incompatibleClassChange` | `IncompatibleClassChangeError` (21: `AbstractMethodError`, JDK-8356942) | yes (4/30) | no |
| `overrideAdded` | — | links, runs `B` | same | no | yes (26/78) |
| `pulledUp` | — | links, runs `A` | same | no | yes (14/50) |
| `methodBecomesPrivate` | DirectMissingMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (18/41) | no |
| `methodBecomesPackagePrivate` | InaccessibleMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (18/41) | no |
| `classBecomesPackagePrivate` | InaccessibleClassProblem | `illegalAccess` | `IllegalAccessError` | yes (16/23) | no |
| `methodBecomesProtected` | InaccessibleMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (12/41) | no |
| `methodBecomesProtectedSub` | InaccessibleMethodProblem | links, runs `p1.A` | same | yes (12/41) | no |
| `methodBecomesProtectedOther` | InaccessibleMethodProblem | `verify` | `VerifyError` | yes (12/41) | no |
| `overrideCutByPackage` | InaccessibleMethodProblem | links, runs `p1.A` | same | yes (18/41) | no |
| `overrideBecomesPrivate` | — | links, runs `A` | same | yes (22/110) | yes (15/110) |
| `superCallPulledUp` | — | links, runs `A` | same | no | yes (20/69) |
| `superCallRemoved` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (22/69) | no |
| `superCallAbstract` | AbstractClassProblem | `abstractMethod` | `AbstractMethodError` | yes (25/41) | no |
| `defaultSuperCallAbstract` | DirectAbstractMethodProblem | `abstractMethod` | `AbstractMethodError` | yes (7/23) | no |
| `staticIfaceMethodRemoved` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (9/23) | no |
| `staticMovedToIface` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (11/34) | no |
| `defaultBecomesStatic` | VirtualStaticMemberProblem | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (9/23) | no |
| `defaultBecomesPrivate` | DirectMissingMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (9/23) | no |
| `fieldRemoved` | MissingFieldProblem | `noSuchField` | `NoSuchFieldError` | yes (34/57) | no |
| `fieldBecomesStatic` | VirtualStaticMemberProblem | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (34/57) | no |
| `fieldBecomesFinal` | — | `illegalAccess` | `IllegalAccessError` | yes (17/57) | no |
| `fieldBecomesPrivate` | MissingFieldProblem | `illegalAccess` | `IllegalAccessError` | yes (34/57) | no |
| `fieldShadowed` | — | links, runs `B` | same | no | yes (42/165) |
| `fieldIfaceBeforeSuper` | — | links, runs `I` | same | yes (37/224) | yes (37/224) |
| `putstaticBecomesFinal` | — | `illegalAccess` | `IllegalAccessError` | yes (13/49) | no |
| `methodBecomesFinalBehind` | — | `finalOverride` | `IncompatibleClassChangeError` | no (0/69); its own client breaks, but no client of `space3` is in `A`'s package | no |
| `transitiveOverride` | — | links, runs `X` | same | no (0/60) | no (0/60); the case's own client changes, but no client of `space3` has the shape |
| `classBecomesSealed` | — | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (15/32) | no |
| `classBecomesSealedPermitting` | — | links | same | no | no |
| `ifaceBecomesSealed` | — | `incompatibleClassChange` | `IncompatibleClassChangeError` | yes (7/14) | no |
| `sealedPermitsNonPublicElsewhere` | — | `incompatibleClassChange` | `IncompatibleClassChangeError` | no (0/32) | no |
| `sealedPermitsPublicElsewhere` | — | links | same | no | no |
| `ctorRemoved` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (9/41) | no |
| `ctorBecomesPrivate` | DirectMissingMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (9/41) | no |
| `ctorBecomesPackagePrivate` | InaccessibleMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (9/41) | no |
| `ctorPulledUp` | DirectMissingMethodProblem | `noSuchMethod` | `NoSuchMethodError` | yes (13/86) | no |
| `ctorPulledUpPrivate` | DirectMissingMethodProblem | `illegalAccess` | `IllegalAccessError` | yes (13/86) | no |
| `ctorClassBecomesAbstract` | AbstractClassProblem | `instantiation` | `InstantiationError` | yes (27/41) | no |

MiMa 1.2.1 is silent on five cases that break some client: `defaultConflict`, `overrideBecomesPrivate`, `fieldIfaceBeforeSuper`, `fieldBecomesFinal` and `putstaticBecomesFinal`. Track B explains each as a gap.

## Not modelled

Nestmates (private access is same-class only); method bodies, so a library method's own calls and constants folded into the client (Track J4); `Object`'s methods in interface resolution; protected constructors and constructor chaining between library classes; signature-polymorphic methods, loader constraints, class initialisation, modules. The open ones are in [`docs/roadmap.md`](../../../docs/roadmap.md).

## PRs

- [retronym/talks#50](https://github.com/retronym/talks/issues/50): HotSpot calibration, client spaces, fields, access and `invokespecial` (Tracks J1–J3).
- [retronym/talks#63](https://github.com/retronym/talks/issues/63): sealed classes and constructor call sites (Track J5).
