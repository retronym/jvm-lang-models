# Track J — JVM linkage (`Jvm/`)

## Problem

Zinc asks whether a client must be *recompiled*; binary compatibility asks whether its old classfile still *links*, and runs the same code, against an edited library. Both are questions about a task's trace against an edited environment. The Zinc toys model erasure and forwarders inside each feature file, but nothing modelled linkage itself, so there was no ground truth to check MiMa against (Track B) and nothing for the Scala and Java front ends (Tracks S and V) to lower to.

## What was built

- **[`packages/jvm/Jvm/Link.lean`](../Jvm/Link.lean).** Linking as a `Task` over the class table: loading checks, resolution (JVMS §5.4.3.2–4), selection (§5.4.6) and access (§5.4.4, plus the verifier's receiver, `invokespecial` and protected rules). Its trace is the client's *linkage footprint*, so T1 applies unchanged: [`link_congr`](../Jvm/Link.lean#L782). `Compatible` and [`compatible_of_footprint`](../Jvm/Link.lean#L801) state binary compatibility and prove it where the edit misses the footprint.
- **The contract.** [`Jvm.World`](../Jvm/Link.lean#L122) (classfiles), [`Jvm.Program`](../Jvm/Link.lean#L760) (what a client loads and executes) and [`Jvm.Site`](../Jvm/Link.lean#L72). Front ends produce a `World`; consumers read one. These types were changed only additively.
- **Sites as javac emits them.** `C c = new R(); c.m()` is `new R; invokespecial R.<init>; invokevirtual C.m`, so the verifier's upcast check, instantiation and load-on-reference are part of `Site` semantics. `Site.construct c n d` is `new c(…)`.
- **[`packages/jvm/Jvm/Catalogue.lean`](../Jvm/Catalogue.lean).** Library edits, each with MiMa's expected problem, linked before and after by kernel `decide`.
- **[`packages/jvm/Jvm/Clients.lean`](../Jvm/Clients.lean).** `breaksSomeClient k`: some client in a bounded space links on `v0` and fails on `v1`. `changesSomeClient k`: some client links on both and runs a different method (the first form of "links, but runs different code"). Clients must be well-typed against `v0`. Three spaces: `space` (an optional client class `X` and one call site of any kind), `space3` (adds fields, `invokespecial`, interface statics, sites inside `X`), `space5` (constructors and `new`). Their sizes, and the catalogue's, are generated into [`docs/stats.md`](../../../docs/stats.md#jvm-catalogue-and-client-spaces).
- **Method bodies (Track J4).** A method's body is its linkage behaviour: the sites it runs, in order, when it runs straight through once ([design](track-j4-design.md)). Sites gain `this` as a receiver; the run enters the selected method and runs its body from its class, and a program's outcome is the sequence of methods entered. [`SameBehaviour`](../Jvm/Link.lean#L795) is outcome equality, and `changesSomeClient` is stated on it.
- **The HotSpot probe.** `lake exe jvmcases` dumps the catalogue and spaces as JSON lines; [`packages/jvm/probes`](../probes) renders each case's `v0`, `v1` and client with the Classfile API (version 65), each method logging its owner on entry and then running its body, runs the client against both, and compares the `Throwable` or the sequence of methods entered. `OUT=dir` keeps the classfiles for MiMa.
- **No `native_decide`** (review finding 7). Catalogue witnesses use `decide`; client-space verdicts use `decide +kernel`, since the elaborator's `decide` hits its recursion limit.

Steps:
- Track J1: calibrate the catalogue on HotSpot. Done.
- Track J2: client spaces and verdicts. Done.
- Track J3: fields, `invokespecial`, private methods, static and private interface methods, access control, the protected check. Done, except the smaller items in [`docs/roadmap.md`](../../../docs/roadmap.md); nestmates came with Track J4.
- Track J5: sealed classes (`PermittedSubclasses`) and constructor calls. Done.
- Track J6: overriding along a chain of library classes, the shape of JVMS §5.4.5's example: `chainSpace` in [`Clients.lean`](../Jvm/Clients.lean) (`lake exe jvmcases chain`). Done; it found two model bugs, below.
- Clients in the library's package and a space over two client classes: done by `chainSpace` (client class `J` in package 0, 1 or 2 beside `X`); the catalogue's spaces still have one client class, in the unnamed package.
- Track J7: default methods along a chain of superinterfaces, `K extends J extends I`, with an interface `B` off the chain: `defaultsSpace` in [`Clients.lean`](../Jvm/Clients.lean) (`lake exe jvmcases defaults`), built with the space builder (`Part`, `⊗`, `build`). Done; it found one model bug, below.
- Track J8: field resolution through superinterfaces at depth (JVMS §5.4.3.2): `fieldsSpace` in [`Clients.lean`](../Jvm/Clients.lean) (`lake exe jvmcases fields`). Done; the model agreed from the start.
- `Object`'s methods in interface resolution (JVMS §5.4.3.4 step 2): `Object` in the class table where a case needs it, `objectSpace` in [`Clients.lean`](../Jvm/Clients.lean) (`lake exe jvmcases object`). Done.
- Track J4: behaviour, in the steps of its [design](track-j4-design.md). Bodies and the run, the probe, the body space (`bodySpace`, `lake exe jvmcases bodies`), the 17 reversed edits (Track B), Scala and Java bodies (Tracks S and V) and nestmates (`nestSpace`, `lake exe jvmcases nests`): done. Constants folded into the client are the Java layer's ([`Jls13.lean`](../../java/Java/Jls13.lean)).

## Results

**Calibration.** On Temurin 21.0.12, 25.0.4 and 27, the probe agrees with the model on every catalogue case and on every program of `space`, `space3`, `space5`, `chainSpace`, `defaultsSpace`, `fieldsSpace`, `objectSpace`, `bodySpace` and `nestSpace`, apart from two known HotSpot bugs on JDK 21, below. Runs from Track J6 on are recorded in the [calibration ledger](../probes/runs/README.md), one line per run with its commit; the last full run is at `ba79791`: catalogue 52 cases, `space` 65,391 programs, chain 28,800, defaults 63,000, fields 33,600, object 3,600, 0 disagreements on each JDK. Its lines after the first say `dirty: true` only because `probe.sh`'s exclusion of the ledger did not match files, so the ledger's own new lines counted; fixed since.

**[`LinkError`](../Jvm/Link.lean#L164) to the JVM's exceptions**, the same on all three JDKs: `noClassDef` → `NoClassDefFoundError`, `incompatibleClassChange` → `IncompatibleClassChangeError`, `noSuchMethod` → `NoSuchMethodError`, `noSuchField` → `NoSuchFieldError`, `abstractMethod` → `AbstractMethodError`, `instantiation` → `InstantiationError`, `illegalAccess` → `IllegalAccessError`, `verify` → `VerifyError`. `finalSuper` and `finalOverride` are `IncompatibleClassChangeError`, not `VerifyError`.

**Track J7.** `defaultsSpace`: interfaces `I`, `J extends I`, `K extends J` each declare `m()V` as a default, abstract, static or private method or not at all; a library class `A` implements none, `I`, `K`, both, or `K` and an off-chain interface `B` with a default or abstract `m`, and declares `m` public, package-private or not at all; the client's `X` extends `A` or implements one interface, and declares a public `m` or not; one `invokeinterface` of `I.m`, `J.m`, `K.m` or `invokevirtual` of `A.m`, `X.m` on an `X`, from a client class in package 0, 1 or 2. 63,000 programs. Before the fix below, 2,412 disagreements on HotSpot 25, all one rule; after it, 0 on 21, 25 and 27, with the JDK-8356942 programs on 21 as known deviations. JDK 17 cannot run the probe (it renders version-65 classfiles).

**Track J8.** `fieldsSpace`: `A` (package 1) implements `I`; `B extends A` (package 2) implements `J`, and `J extends K`. `A` and `B` each declare a `String` field `m`, public, protected, package-private or private, static or not, or public and final, or none; each interface declares a constant `m` or none; one `getfield`, `putfield` (owners `A`, `B`, `X`) or `getstatic`, `putstatic` (also `J`) on the client's `X extends B`, from a client class in package 0, 1 or 2. 33,600 programs, 0 disagreements on 21, 25 and 27, with no change to the model: §5.4.3.2's order (the class, its superinterfaces recursively, then the superclass) holds at depth, where it had one witness. `fieldIfaceDepthBeforeSuper` is the javac-reachable form one level down from `fieldIfaceBeforeSuper` ([scala-garden/mima#995](https://github.com/scala-garden/mima/issues/995)): `B.m` reads `K.m`, found through `J`, before `A.m`.

**`Object`'s methods.** An interface's `super` is its classfile's `super_class`, `Object`, and `resolveIface` looks there between the interface itself and its superinterfaces: a public instance method of `Object` resolves an interface method reference (§5.4.3.4 step 2). `Object` ([`Catalogue.object`](../Jvm/Catalogue.lean#L552)) has a public `hashCode()I` and a protected `finalize()V`, and is in a package of its own. `ifaceHashCodeRemoved`: an interface drops `int hashCode();` and `i.hashCode()` still links to `Object`'s (without step 2 the model said `noSuchMethod`); `ifaceFinalizeRemoved`: an interface drops `void finalize();` and the call fails, since step 2 takes only public methods. `objectSpace` varies `hashCode` and `finalize` over `I`, `J extends I` and the client's `X`, with `invokeinterface` and `invokevirtual` sites from packages 0, 1 and 2: 3,600 programs, 0 disagreements on 21, 25 and 27. Its first run had two kinds of disagreement, neither a rule of [`Link.lean`](../Jvm/Link.lean): `Object` was in the unnamed package, so the model let a client in that package reach the protected `finalize` (720 programs; HotSpot: IllegalAccessError); and `finalize` methods of earlier cases' objects ran on the Finalizer thread and overwrote the probe's log (9, scattered), so `probe.sh` now runs with `--finalization=disabled`. A separate space rather than a column of `defaultsSpace`, where these sites would repeat over every declaration of `m`.

**What calibration added to the model.** Each of these was a disagreement first, and is now a rule:
- Loading a class checks that its superclass and superinterfaces are accessible (`IllegalAccessError`).
- The verifier's `invokespecial` rule turns on whether the referenced class is an interface, not on the constant's tag. An `InterfaceMethodref` to a class passes the verifier and fails resolution with ICCE; a reference to an interface that is not a direct superinterface is a `VerifyError`.
- The protected-receiver check (§4.10.1.8), predicted by `methodBecomesProtectedOther`.
- `PermittedSubclasses` (JVMS §5.3.5) is checked after the final-superclass check and before the access check, as HotSpot's class file parser does: the class must be listed and, unless public, in the sealed type's run-time package.
- A constructor resolves like any method, walking superclasses with an access check, and must then be declared by `c` itself (JVMS §6.5 `invokespecial`, linking exceptions), so an inherited match is `noSuchMethod` (`ctorPulledUp`). The access check comes first: an inherited private match is `illegalAccess` (`ctorPulledUpPrivate`).
- The final-method check at loading (§5.3.5) looks at every final method of every superclass, not the nearest declaration of the name. Found by Track J6: with a final `A.m` behind a `B.m` that does not override it (private, or package-private elsewhere), the model let `I` or `X` load, and HotSpot 21, 25 and 27 report "overrides final method A.m" (1,836 programs of the chain space). `methodBecomesFinalBehind` is the javac-reachable form, through a client in `A`'s package; MiMa 1.2.1 reports nothing for it, since `A.m` is package-private.
- Transitive overriding (§5.4.5 (b)): a package-private method is also overridden from another package through an intermediate method that overrides it and is overridden in turn. Found by encoding the JVMS's own example as `transitiveOverride`: the model, without (b), predicted `I.m` after the intermediate method became public, and HotSpot 21, 25 and 27 run `X.m`. The calibration spaces had not found it: no client of `space3` declares a package-private method in another package below two library classes.
- `invokeinterface` fails with `IllegalAccessError` if it selects a method that is neither public nor private (JVMS §6.5, run-time exceptions, before the abstract check). The model was missing this clause of the specification; HotSpot follows it. Found by Track J7: a package-private `A.m` can override a public default `K.m` (§5.4.5 only asks that `K.m` be public), so selection on an `X extends A` picks `A.m`; the model ran it, and HotSpot 25 threw "IllegalAccessError: 'void X.m()'" (2,412 of the 40,500 programs then in the space). `pkgMethodAboveDefault` is the javac-reachable form: `A`, not implementing the interface, gains a package-private `m`, and the client's `X extends A implements I` breaks; MiMa 1.2.1 reports nothing (a method was added): a sixth MiMa gap, MiMa-S1, which the corrected rules now report, see [Track B](../../mima/docs/track-b.md). MiMa's 17 reversed edits, with a library hook, found it again (`ifaceHookPackagePrivate`: an interface's default `run()` calls a new abstract `m`, which the client's package-private `m` overrides).


**JVMS §5.3.5's order of loading checks is not HotSpot's.** §5.3.5 resolves the superclass, with its access check, then checks its finality and `PermittedSubclasses`, then the superinterfaces. HotSpot 21, 25 and 27 check the superinterfaces first and a final superclass before an inaccessible one, and the model follows HotSpot: `finalSuperInaccessible` and `ifaceNotIfaceSuperInaccessible` throw `IncompatibleClassChangeError` where the specification gives `IllegalAccessError` (draft: [`jvms-derivation-check-order.md`](../../../docs/upstream/jvms-derivation-check-order.md); the [specification ledger](../../../docs/specification-ledger.md) lists it with the other omissions and contradictions).

**Library bodies need no new rule (Track J4).** `bodySpace` runs a library method's own call of `m` (`this.m()`, a static `m()`, `new B().m()`, `super.m()`, `new A().m()` from another package, or the field `this.m`) against every state of `A.m`, with the client's `X` below. On HotSpot 21, 25 and 27 the probe agrees with the model on all 4,752 programs, with the rules the client sites already had: `AbstractMethodError` inside `run` for a hook the client does not implement, `IllegalAccessError` for a private or package-private `A.m` called from `B`'s body in another package, a write to a final field outside `<init>`, and the verifier's protected check for `new A().m()` in `B`. The catalogue's `hookBecomesAbstract` and `hookBecomesPrivate` are edits whose breaking or changed client is the library's own call. Re-running `space` and `chain` with empty bodies through the new probe gave 0 disagreements.

**Nestmates (Track J4).** `Header` carries `NestHost` and `NestMembers`, and a private member is accessible from the classes of its nest (JVMS §5.4.4): `cur` and the declaring class have the same nest host, where a class's host is the class its `NestHost` names if that class is present, in the same run-time package and lists it, and otherwise the class itself. `nestSpace` reaches a private member of `A` from `B`'s body or the reverse (a call, a static call, `this.m()` from `B extends A`, a field, a static field), over eight nest configurations and `B` in `A`'s package or not: 544 programs agree with HotSpot 21, 25 and 27 with no further rule. A host that does not list the member, a member that does not name the host, or a member in another package is alone in its nest, without an error of its own, as HotSpot has done since JDK 15. `nestMemberRemoved` and `nestHostChanged` are edits whose only breaking client is the library inner class's body; MiMa does not read the nest attributes.

**Known JDK bugs hit by the probe**, both fixed in JDK 25. The model follows the JVMS; the probe reports the JDK 21 results as known deviations.
- [JDK-8356942](https://bugs.openjdk.org/browse/JDK-8356942): `invokeinterface` on a receiver with two maximally-specific defaults throws `AbstractMethodError` instead of ICCE (`defaultConflict`, and 264 programs of `defaultsSpace`, all with `A` implementing `B` and `K`). Regressed in JDK 10.
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
| `hookBecomesAbstract` | DirectAbstractMethodProblem | `abstractMethod` (inside `A.run`) | `AbstractMethodError` | its own client | no |
| `hookBecomesPrivate` | DirectMissingMethodProblem | links, enters `A.run`, `A.m` | same | no | its own client |
| `ifaceHookPackagePrivate` | ReversedMissingMethodProblem | `illegalAccess` (inside `J.run`) | `IllegalAccessError` | its own client | no |
| `nestMemberRemoved` | — | `illegalAccess` (inside `B.run`) | `IllegalAccessError` | its own client | no |
| `nestHostChanged` | — | `illegalAccess` (inside `B.run`) | `IllegalAccessError` | its own client | no |

MiMa 1.2.1 is silent on five cases that break some client: `defaultConflict`, `overrideBecomesPrivate`, `fieldIfaceBeforeSuper`, `fieldBecomesFinal` and `putstaticBecomesFinal`. Track B explains each as a gap.

## Not modelled

Data and control flow in method bodies; a constructor's implicit `super(…)` call; `Object` beyond `hashCode` and `finalize`, and as the superclass of a client class that names none (so such a class does not get `Object`'s protected access); protected constructors and constructor chaining between library classes; signature-polymorphic methods, loader constraints, class initialisation, modules. The open ones are in [`docs/roadmap.md`](../../../docs/roadmap.md).

## PRs

- [retronym/talks#50](https://github.com/retronym/talks/issues/50): HotSpot calibration, client spaces, fields, access and `invokespecial` (Tracks J1–J3).
- [retronym/talks#63](https://github.com/retronym/talks/issues/63): sealed classes and constructor call sites (Track J5).
