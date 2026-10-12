# Roadmap: open work

## Why

The Lean model was built to answer one question: is Zinc's invalidation sound, relative to obligations on the compiler bridge? To answer it, each feature file (`Erasure`, `Hier`, `Flat`, `Inline`, `Names`, …) has its own toy language, sized to what Zinc hashes. The toys found real bugs, but they are private to one consumer. Factored out, the same knowledge answers other questions:

- **Binary compatibility.** Zinc asks whether a client must be *recompiled*; MiMa asks whether its old classfile still *links*. Both are questions about a task's trace against an edited environment, so T1 applies to linkage unchanged ([`link_congr`](../packages/jvm/Jvm/Link.lean#L591)).
- **IDE type systems.** The TCK (`retronym/scala-type-system-tck`) checks IntelliJ against an `asSeenFrom` model that now shares its core with the Scala layer.
- **Scala 2 → 3 migration.** The name-resolution calibration in [talks#21](https://github.com/retronym/talks/issues/21) is already a list of differences between the two compilers.

## Architecture

The layers and their imports are in [the root README](../README.md#packages). [`Jvm.World`](../packages/jvm/Jvm/Link.lean#L74), [`Jvm.Program`](../packages/jvm/Jvm/Link.lean#L572) and [`Jvm.Site`](../packages/jvm/Jvm/Link.lean#L421) are the contract between them: a front end turns sources into classfiles and a client program; a consumer reads them. Each layer is calibrated against its real tool before claims are built on it.

## Done

The TCK's dependency on `asSeenFrom` is resolved: the IntelliJ model is [`packages/intellij`](../packages/intellij), on top of `ScalaTypes.AsSeenFrom`, and the TCK pins it ([retronym/scala-type-system-tck#9](https://github.com/retronym/scala-type-system-tck/issues/9)).

Each track's results, calibration numbers and PRs are in its own file:

| Track | Layer | Results |
|---|---|---|
| Tracks J1–J3, J5–J8 | JVM linkage, overriding along library chains, default methods along superinterface chains, field resolution through superinterfaces, `Object`'s methods in interface resolution, calibrated on HotSpot 21/25/27 over its client spaces | [`packages/jvm/docs/track-j.md`](../packages/jvm/docs/track-j.md) |
| Tracks S1–S6 | Scala lowering (2.12, 2.13, 3), shared `asSeenFrom`, membership; calibrated on scalac | [`packages/scala/docs/track-s.md`](../packages/scala/docs/track-s.md) |
| Tracks V1–V3 | Java lowering, JLS chapter 13; calibrated on javac 17/21/25 | [`packages/java/docs/track-java.md`](../packages/java/docs/track-java.md) |
| Tracks B1, B2, B4 | MiMa modelled, five gaps (MiMa-F1, MiMa-M1, MiMa-F2, MiMa-D1, MiMa-P1), corrected rules; Zinc-clean ⇒ binary-compatible | [`packages/mima/docs/track-b.md`](../packages/mima/docs/track-b.md) |

## Open

### Track J4: behaviour

**Why.** The JVM model links but runs no code. A library method's own calls are invisible, so MiMa's 17 `ReversedMissingMethodProblem` reports that break no client in the model are unjudged, and nestmates can't be modelled usefully (a nest change breaks a client only through a library method's own calls). Constants folded into the client are part of the same gap.

**Done looks like.** Method bodies as a list of sites linked when the method runs; constants folded at the client; `changesSomeClient` generalised to "links, but runs different code"; the 17 reports classified on HotSpot. Track: [`packages/jvm/docs/track-j.md`](../packages/jvm/docs/track-j.md).

### Track J3 remainder: nestmates and smaller linkage gaps

**Why.** These are what [`packages/jvm/Jvm/Link.lean`](../packages/jvm/Jvm/Link.lean) still says it doesn't model, and each can hide a MiMa gap.

**Done looks like.** Nestmates (`NestHost`/`NestMembers`, private access between members; after Track J4); protected constructors and constructor chaining between library classes. Each calibrated on HotSpot like the rest. Clients in the library's package and a space over two client classes are done by Track J6's `chainSpace` (client class `J` in package 0, 1 or 2 beside `X`); the catalogue's own spaces still have one client class, in the unnamed package. Track: [`packages/jvm/docs/track-j.md`](../packages/jvm/docs/track-j.md).

### Next seams

Each is one shape, one space and one probe run, as Track J6 was.

- **`var` and constructor parameters in the source models.** Scala setters (where scalac 2's trait-setter `AbstractMethodError` lives) and constructor parameters, `var` in Java; they widen Track B3 directly (see the layer remainders below).

### Track B3: source-level spaces

**Why.** MiMa's users edit source, not classfiles. The JVM edit space found MiMa's gaps; a source edit space would find which ones real Scala and Java edits reach, and where scalac's encoding (forwarders, `$init$`, value classes) makes a source-compatible-looking edit break.

**Done looks like.** A space of source edits, Scala and Java, lowered, linked against a client space and checked against MiMa and HotSpot, as the JVM edit space was. Today only the Scala catalogue's first cases have been run through MiMa, and the Java catalogue not at all. Track: [`packages/mima/docs/track-b.md`](../packages/mima/docs/track-b.md).

### A sixth MiMa gap: a package-private method above a default

**Why.** Track J7's `pkgMethodAboveDefault`: a public class gains a package-private `m()`, and a client subclass in another package that inherits a default `m()` from an interface now fails `invokeinterface` with `IllegalAccessError` (JVMS §6.5). MiMa 1.2.1 and the corrected rules are both silent; no key covers a package-private member added to a public class.

**Done looks like.** A corrected rule in [`packages/mima/MiMa/Fixed.lean`](../packages/mima/MiMa/Fixed.lean) that reports it (for example, a package-private method added to a public, non-final class whose name and descriptor some superinterface of a possible subclass could declare), an edit-space shape that reaches it, and `Sound` re-run; or a reasoned scope line. Track: [`packages/mima/docs/track-b.md`](../packages/mima/docs/track-b.md).

### A general proof for the corrected MiMa rules

**Why.** [`packages/mima/MiMa/Sound.lean`](../packages/mima/MiMa/Sound.lean) checks the corrected rules on the edit space only. Upstreaming them to MiMa is stronger with a proof that they are sound for every library.

**Done looks like.** A theorem that if `Fixed` reports nothing, every client that linked on the old library links on the new one, for all libraries. It needs a monotonicity argument about resolution and selection over the whole `Jvm` model. Track: [`packages/mima/docs/track-b.md`](../packages/mima/docs/track-b.md).

### Port `Hier`, `Erasure`, `Flat` and `ImplicitScope` onto the shared Scala layer

**Why.** These four `Zinc/` files each have their own toy Scala, their own `asSeenFrom` and their own query plumbing. No `Zinc/` file imports [`packages/scala-types/ScalaTypes/AsSeenFrom.lean`](../packages/scala-types/ScalaTypes/AsSeenFrom.lean) or [`packages/scala/Scala/Lower.lean`](../packages/scala/Scala/Lower.lean). Until they do, Zinc's bridge instances, Track B4 and the MiMa model don't share one Scala semantics, and Track B4's key model ([`ZincBridgeKeys.lean`](../packages/links/Links/ZincBridgeKeys.lean)) stays separate from the Zinc one.

**Done looks like.** The four files restated over `ScalaTypes.AsSeenFrom`, `ScalaTypes.Resolve` and `Scala.Lower`, with their theorems kept (`Task` is already in its own package, `query`); the explicit-interface T3 that Track B4 restates in [`packages/links/Links/ZincBridge.lean`](../packages/links/Links/ZincBridge.lean) moved into [`General.lean`](../packages/inc-comp/IncComp/General.lean). Single-writer work, since it touches `Zinc/`. Track: [`packages/scala/docs/track-s.md`](../packages/scala/docs/track-s.md).

### Scala and Java layer remainders

**Why.** Each widens what Track B3's source spaces can express.

**Done looks like.** Membership: type members, `var`, `protected` and qualified access, `abstract override`, objects as overriders, and a probe of the Java rules. Lowering: case classes with type parameters or several parameter lists, enums with type parameters, objects nested in classes, local classes, constructor parameters of plain classes, `lazy val` and `var` in classes, overloading, Java-defined parents. Tracks: [`packages/scala/docs/track-s.md`](../packages/scala/docs/track-s.md), [`packages/java/docs/track-java.md`](../packages/java/docs/track-java.md).

### Drive the compilers from a long-lived harness

**Why.** The calibration probes start a fresh JVM for every compiler invocation. [`packages/scala/probes/members.py`](../packages/scala/probes/members.py) batches a space into one `scala-cli compile --server=false` per round per compiler, and needs rounds only because an error in one program stops refchecks for the whole batch; [`packages/mima/probes/scala.sh`](../packages/mima/probes/scala.sh) launches `scala.tools.nsc.Main` once per case; ad-hoc checks of a single shape (as for `Flat`'s refchecks against scalac and dotc) pay JVM start-up and a cold JIT per program. That caps the spaces we calibrate on at a few thousand programs, where the exhaustive checks run over hundreds of thousands (`Flat`'s 216,000), and it makes per-program results depend on batching.

**Done looks like.** One server per compiler version (scalac 2.12, 2.13, dotc 3; javac through `javax.tools`), started once and kept warm: it reads a program (sources, options, optional classpath of earlier outputs, for separate compilation) on stdin, compiles it in a fresh run of a reused `Global` or `Driver`, and answers with the diagnostics (file, line, kind) and the classfiles' digests or bytes, so each program is compiled on its own and an error in one cannot hide another's. The probes then talk to the servers instead of spawning compilers, and the shared semantics can be checked against the compilers on the same spaces the exhaustive checks use (`FlatRules.cfgs`, `HierShared.space`). Prior art: the TCK's reference engine (retronym/scala-type-system-tck `reference/`) keeps an `nsc.Global` in process; Bloop and scala-cli's build server do the same for builds. Track: [`packages/harness`](../packages/harness).

### Upstream reports

**Why.** Findings help no one until filed.

**Pace.** The fixes in forks (retronym/zinc, retronym/scala, retronym/scala3) stay as drafts for now, so as not to overwhelm the maintainers; they move upstream a few at a time.

**Done looks like.** Four MiMa issues are filed ([scala-garden/mima#993](https://github.com/scala-garden/mima/issues/993)–#996; MiMa-D1 is out of MiMa's scope, see [`packages/mima/docs/track-b.md`](../packages/mima/docs/track-b.md)). The scalac 2 trait-setter `AbstractMethodError` is filed as [scala/bug#13199](https://github.com/scala/bug/issues/13199), with the draft fix [retronym/scala#136](https://github.com/retronym/scala/issues/136) to open as a PR once the direction is agreed.

### Contributors

**Why.** The model has one author plus agents. This repository's packages are now separable enough for outside contributors, through the tiers in the contributor proposal.

**Done looks like.** A first set of tiered tasks, per package, linked from each package README.
