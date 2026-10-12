# Phase 29 — `Hier`, `Flat`, `Erasure` and `ImplicitScope` on the shared Scala layer

## Problem

Four `Zinc/` files each define their own toy Scala: class and type enums, a parent walk, a type-argument substitution standing in for `asSeenFrom`, and a query type for the walk. `HierShared` and `FlatShared` embed two of them into `ScalaTypes` and check agreement on bounded spaces, which found real gaps (Hier's depth-first walk on diamonds; two `Members` gaps from `Flat`). But agreement on a space is evidence, not sharing: the next edit to either side can drift, and the Zinc bridge instances, Track B4 (`Links`) and MiMa still do not reason about one Scala semantics. As the shared layer grows (membership, lowering, erasure), every toy is one more copy to keep in step.

Goal: each of the four files *uses* the shared walk, `asSeenFrom`, and (where relevant) refchecks and erasure, so that its theorems are about the same semantics `Scala.Lower` and `Scala.Members` compute. The toys survive only as front ends: small enumerable syntaxes that build [`Scala.Decl`](../../scala-types/ScalaTypes/Syntax.lean#L97)s, so the exhaustive spaces stay enumerable.

## The crux: query granularity

The shared layer reads other definitions through one coarse query, `Scala.Q.decl n isObj`, answered with the whole `Decl`. That is what lowering needs (it reads everything), and it is what Track B4's `searched` bridge keys on.

Hier's designs differ exactly in how finely they key the walk. `D` records `(c, name n)` for "does `c` declare `n`" and `(c, parents)` for `c`'s header; `W` and `Mk` differ in where the walk runs. If Hier's walk asked `Q.decl`, `D`'s only sound key would be the whole declaration, and the precision ladder collapses. Concretely, scenario 1 (`A.m : Int → String`): `Z` selects `B.g`, its walk reads `A`, and with a whole-decl key `Z` recompiles; today `D` recompiles `[X, Y]` only. Flat's header rule and Erasure's per-name witnesses have the same shape.

So the walk must be expressible over *fine* queries, and the coarse form must be the same code, not a second copy.

## Key decisions

1. **Fine queries in the shared layer.** [`Scala.Q`](../../scala-types/ScalaTypes/Resolve.lean#L18) gains `header n` (type-parameter count, kind, parents, the facts `lin` reads) and `member n m` (the definition's own non-`fieldOnly` member named `m`). `decl` stays for consumers that read everything (`Lower`, `Members`, `Links`). [`Program.envIn`](../../scala-types/ScalaTypes/Resolve.lean#L33) answers all three from the same `Decl`, so a fine answer is by construction a projection of the coarse one.

2. **One walk, generic in how it reads.** `lin` and first-member lookup are written once, parametric in a reader (`header`, `member` as `M` actions). The coarse instance reads through `need` and is today's `lin`/`hits` (same results; the trace is the same set of `decl` queries); the fine instance asks `header`/`member`. Written by structural recursion rather than `for … in`, so trace lemmas are provable. One theorem in `ScalaTypes`: under `Program.env p`, the fine and coarse walks give the same result for every program. That replaces `HierShared`'s exhaustive agreement check for the parts that become shared code.

3. **Trace lemmas once.** "The walk asks only `header` and `member` queries" and its congruence corollary (two environments agreeing on those answers give the same walk) are proved in `ScalaTypes`. `HierSound`'s `trace_linT`/[`trace_firstDecl`](../Zinc/Bridges/HierSound.lean#L55)/[`trace_mergeWith`](../Zinc/Bridges/HierSound.lean#L25)/[`resolveFrom_congr`](../Zinc/Bridges/HierSound.lean#L151) become uses of them, and Flat and Erasure reuse them.

4. **Query translation in `query`.** A generic fold of a task through a query interpretation, `Task.interp : ((q : Q) → Task Q' A' (A q)) → Task Q A α → Task Q' A' α`, with `run`/`trace` lemmas. Each Zinc file maps shared queries into its framework shape `(Cls × Q)` with it (a `Cls`-less name is answered `none` without a query). [`Links.ZincBridge.tr`](../../links/Links/ZincBridge.lean#L173)/`back`/`fq` become an instance.

5. **Toys as front ends.** `Cls`, `Name` and a small `Ty` stay, as the syntax the scenarios and spaces are written in; `toScala` (today in `HierShared`) becomes the front end, and interfaces store [`Scala.Decl`](../../scala-types/ScalaTypes/Syntax.lean#L97). [`Hier.Ty.subst`](../Zinc/Bridges/Hier.lean#L49), `mergeWith`, `linT`, `firstDecl` are deleted. Materialised members (`W`) store `Option Scala.Ty`.

6. **Results kept, or the change explained.** Every `D`/`W`/`Mk` obligation theorem and every scenario `Report` should be unchanged. If a report moves (for instance because the shared lookup reads a different set of classes than Hier's early-stopping `firstDecl`), that is a finding about Hier, written down here, not a reason to keep a private walk.

Rejected: keeping the coarse query and keying `D` on whole declarations (loses the precision results above); keeping per-file walks plus agreement checks (today's state: coherence only on the space checked).

## Order, and what each port needs

| step | file | needs from the shared layer | status |
|---|---|---|---|
| 1 | `query`: [`Task.interp`](../../query/Query/Interp.lean#L20) | — | TODO |
| 2 | `ScalaTypes.Resolve`: fine queries, generic walk, fine = coarse, trace lemmas | — | TODO |
| 3 | `Hier`, `HierSound`, `HierShared` (template) | steps 1–2 | TODO |
| 4 | `Flat`, `FlatShared` | stored linearization over `header`; refchecks prelude against `Members` (its gaps: `var`, the 2.13 re-check, Scala 3's direct-parent rule are already characterised in `FlatShared`) | TODO |
| 5 | `Erasure` | `Lower.erase`; additions: `Long`, intersection types (`W with Z`, erasing by trait-or-class), so `header` must carry the kind | TODO |
| 6 | `ImplicitScope` | base classes from the shared walk; implicit search over companions is not in the shared layer (decision below) | TODO |
| 7 | Track B4's explicit-interface T3 into [`General.lean`](../../inc-comp/IncComp/General.lean) (roadmap item) | — | TODO |

Each step builds, keeps its theorems, and is one commit.

## Open questions

- **ImplicitScope.** Extend `ScalaTypes` with implicit definitions and a companion-based implicit-scope search (a real, calibratable piece of Scala semantics), or port only the base-class walk and leave the search local, listed as a gap? The first is more work but is the same argument as for the other three.
- **Early stop.** Hier's lookup stops at the first declaring class; scalac's `findMember` reads every base class. For keys, early stop gives the smaller sound trace. Plan: the shared fine lookup early-stops, with `firstHit = (hits l n).head?` proved, so `Members` (which needs all hits) and Hier share `memberOf`.
