# Track J4: behaviour. Design

12 October 2026, for review before code. Track J4 is the open item in [`track-j.md`](track-j.md): the model links but runs no code.

## Problem

[`Jvm.Program`](../Jvm/Link.lean#L646) is a list of classes to load and sites to execute, each site run from a static method of a client class. A library method is a [`MethodInfo`](../Jvm/Link.lean#L87) with flags and no body. So a library method's *own* sites are invisible, and four things cannot be judged:

- **MiMa's `ReversedMissingMethodProblem`.** 17 of the edit space's reported edits break no client of the space, because the only client they break is one whose subclass is called *by the library*: `A.run()` calls `this.m()`, the client's `X extends A`, and the edit adds abstract `m` to `A`. HotSpot throws `AbstractMethodError` inside `run`. Today these are "outside the space", neither confirmed nor refuted ([`track-b.md`](../../mima/docs/track-b.md)).
- **Nestmates.** A nest change breaks a client only through a library method's body: the inner class's body accesses a private member of the outer class, and whether that links depends on `NestHost`/`NestMembers` at the time of the call. With no bodies there is nothing to break.
- **Scala's `$init$` and setter chains.** The Scala catalogue already shows the gap as a wrong prediction: `valAddedToTrait` fails *earlier* on HotSpot than in the model, because `new Y` runs `Y.<init>`, which calls `T.$init$(this)`, which calls the trait setter `Y` does not implement. The model says the first failing site is the client's own call. Constructor chaining between library classes, open since Track J3, is the same shape.
- **"Links, but runs different code."** `changesSomeClient` compares the class each client site selects. With bodies it should compare what the program *does*: the sequence of methods entered, including the library's own calls.

Constants folded into the client (JLS §13.4.9) are not part of this track. Folding is a front-end matter and the Java layer already models it: the client's classfile changes while linkage does not ([`Jls13.lean`](../../java/Java/Jls13.lean)). The JVM sees no site for a folded constant.

## What it is

A method body is a list of sites, run in order when the method is entered. Running a site links it exactly as today, and then, if it entered a method, runs that method's body before the next site. A program's outcome is the first error, or the sequence of methods entered.

That is all. No data, no control flow, no exceptions, no `<clinit>`: the body is the method's *linkage behaviour*, the calls and field accesses that HotSpot would resolve and select when the method runs straight through once. It is what MiMa, Zinc and binary compatibility reason about, and it is what the probe can observe with `ProbeLog`.

## Key decisions

**Bodies live in [`MethodInfo`](../Jvm/Link.lean#L87).** `MethodInfo.body : List (Site C N D)`, default empty. The answer to `Q.method c n d` then carries the body, so a body edit changes a footprint query exactly when the body is run, and [`link_congr`](../Jvm/Link.lean#L667) holds unchanged: T1 needs no new argument. Every existing `World`, space and catalogue case keeps its meaning with empty bodies. [`Jvm.World`](../Jvm/Link.lean#L108), `Program` and `Site` change additively, as the contract promises.

**`this` is a receiver.** Today a site's receiver is a runtime class `recv`, instantiated at the site (`new recv; invokevirtual c.m`). Inside a body, the receiver of `this.m()` is whatever the caller instantiated, which for the interesting cases is the client's class. So the run carries a current receiver class, and sites gain `this`-receiver forms (additive constructors; the existing ones are unchanged). Static sites and `new` sites in bodies need nothing new. `invokespecial` from a body is a `super` call from the declaring class, which `within` already expresses.

**The outcome is the entered sequence.** `outcome w p : Except LinkError (List C)` becomes the list of (class, method) entered, in order, with the per-site class as today for sites that enter nothing. `Compatible` is unchanged (links whenever it did). A second relation, same behaviour, is outcome equality; `changesSomeClient` is restated on it and its current examples must still hold (bodies empty, so the sequence is the per-site class list).

**Fuel, not termination.** A body can call a method whose body calls it back. The run already carries `depth` for superclass walks; bodies use the same fuel, and running out is a distinct outcome, not an error the JVM throws. Spaces keep bodies to one or two sites, so fuel never matters there; it only keeps the definitions total.

**The probe observes exactly the outcome.** `Render.java` already makes every rendered method log its owner through `ProbeLog.ran` on entry; it emits the body's sites after that log, with the same `emit` used for client sites and `this` as `aload_0`. `ProbeLog` keeps the list of owners entered instead of the last one, and `Run.java` compares the list and the `Throwable`. The known-deviation handling and the ledger are unchanged.

**The front ends already produce bodies.** [`Scala.ClassOut`](../../scala/Scala/Lower.lean#L94) and [`Java.ClassOut`](../../java/Java/Lower.lean#L142) carry "the invokes of synthesized bodies" (`$init$` calls, forwarders, super calls, bridges) because the probes compare them; `toJvm` drops them today. With bodies in [`MethodInfo`](../Jvm/Link.lean#L87), `toJvm` keeps them, and the Scala catalogue's `valAddedToTrait`, `superCall*` and `traitOverrideAdded` are judged with the library's own calls. That is the first place the design is tested against something the model already got wrong.

## What stays out, and why

- **Data flow and control flow.** Which branch runs, what a field holds, what is passed: none of it changes what links or which method is selected, given the receiver's class. The one place it matters, a receiver whose class depends on data, is approximated by the client's choice of `recv` and `this`.
- **`<clinit>` and initialisation order (JVMS §5.5).** Real and separable: first active use runs a body with its own rules for interfaces and superclasses. Future work, on top of bodies.
- **Exceptions, `invokedynamic`, signature polymorphism, loader constraints.** As before.

## Steps

1. **Bodies and the run.** `MethodInfo.body`, the `this` receiver, the entered sequence as outcome, `changesSomeClient` on same-behaviour. Every existing kernel-decided example and space verdict must hold unchanged; the catalogue's `Model on v1` column is unchanged because bodies are empty.
2. **The probe.** `Render.java` emits bodies, `ProbeLog` records the sequence, `Run.java` compares it. Re-run `space` and `chain` with empty bodies: 0 disagreements, recorded in the ledger.
3. **A body space.** A library `A` with `run()` whose body is one site (`this.m()`, a static call, `new B`, a super call, a field access on `this`), `B` optionally overriding, the client `X` below with `m` in any access or absent; edits over `m` as the edit space does (absent, abstract, static, private, final). Calibrate on HotSpot 21, 25 and 27. Expected rules: `AbstractMethodError` from inside a library method, `IllegalAccessError` for a private `X.m` reached through `this`, and the protected check from a library body.
4. **The 17 reversed edits.** Re-judge MiMa's edit space with `A.run()` calling `this.m()`: each `ReversedMissingMethodProblem` either breaks a client of the body space or is a false positive. Record in `track-b.md`; `Fixed` gains the rule if it lacks one.
5. **Scala and Java bodies.** `toJvm` keeps synthesized bodies. `valAddedToTrait` must now fail at `new Y`, as HotSpot does; the constructor-chaining and `$init$` cases of the Scala catalogue are re-decided and checked on HotSpot through `scala.sh`.
6. **Nestmates.** `NestHost`/`NestMembers` in `Header`, the nest check in `accessible` for private members, catalogue edits (member leaves the nest, host changes) whose breaking client is a library inner class's body, calibrated on HotSpot. Closes the last Track J3 item.

Each step is one commit series with the lints green; steps 3 and 6 each add a Track J line and a Results paragraph to [`track-j.md`](track-j.md), and step 4 a paragraph to [`track-b.md`](../../mima/docs/track-b.md).
