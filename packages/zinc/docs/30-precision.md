# Phase 30 — Precision: what each descendant-rule preset recompiles beyond need

16 October 2026. Item 2.1 of [the Merkle slice](../../../docs/history/reviews/2026-10-16-merkle-slice.md).

## Summary for a busy reader

The Merkle PoC changes which classes Zinc recompiles after an edit to an ancestor: instead of every descendant, only the descendants that a short table of rules says must be recompiled. The question this phase answers is how much that table actually saves, and whether any of its rules can be dropped or tightened without undercompiling.

The method: take every eight-class program in a fixed shape (abstract class `A`, trait `M`, class `B extends A`, class `C extends B with M`, three small clients), apply every single-class edit, and for each rule preset run Zinc's loop as the model has it. For each run, count the classes recompiled beyond the edited one, check that the result equals a clean build, and count two kinds of waste: classes recompiled although nothing they had read changed (the floor for any design that works from recorded dependencies), and classes recompiled although their output did not change (the floor a perfect oracle would reach). 216,000 programs, 5.8 million edits, eight presets, about twelve CPU-hours.

What it says:

- **Every sound preset is sound here**: no undercompile on any of the 5.8 million edits. The deliberately rule-less preset undercompiles 65% of them, so the check is not vacuous.
- **The rules are worth about 2% on this space** (Zinc's default recompiles 2.2% fewer classes than "every descendant"), **and about 60% of what every preset recompiles has unchanged output.** That is the shape of the space talking: each program has two descendants and three clients, and the clients select the edited member, so they must recompile under any design. The PoC's real wins come from hierarchies with hundreds of descendants and few clients per class (Spark's `TreeNode`), which this space does not have. The per-descendant rates transfer; the totals do not.
- **The rule table beats the dependency floor.** The rules skip some classes that did read something the edit changed (they asked "does ancestor `A` declare `m`" and the answer flipped) and stay correct, because what they read did not change the decision. So "recompile whatever read a changed fact" is not the lower bound for a policy that reasons on Zinc's side; "output unchanged" is.
- **Which rules matter.** Narrowing `trait` to classes that mix the trait in directly is the one step that matters (1%); further narrowing to "only when an implemented member changed" buys 0.03% and is not worth having. Dropping `header` would buy another 1% but rests on an invariant not yet checked (every descendant is a `memberRef` client of its parent).
- **One parity fix, found by looking at the samples.** The run prints two concrete programs per batch with every preset's decision. One showed a trait that mixes a trait in being recompiled with unchanged output. Porting the fix to Zinc found Zinc already had it; the model's rendering of the rule was the conservative one, and is now aligned.

What this gives the PoC: a definition of precision in the framework (`Necessary`, `necessary_invalidated`, [`policyOver_mono`](../../inc-comp/IncComp/General.lean#L222)), a number per preset to cite, and a reusable dashboard (`lake exe exhaustive precision 100`, ten seconds) that shows the loop's work as it runs.

## Question

The Merkle PoC's claim is precision: with the inheritance edge filtered by `DescendantRule`s, an ancestor edit recompiles clients and the descendants that read the change, not the hierarchy. The rule table went from eight rules to six by ablation on scripted tests, `traitDirect` was narrowed after the Spark cross-module run, and two narrowings sit in future work. Each of those is a question of the form "which preset recompiles what, and how much of it was needed", and the framework had no definition of "needed". [`FlatRules.lean`](../Zinc/Bridges/FlatRules.lean) decided soundness per preset over its 216,000 configurations; this phase adds the precision count beside it.

## The definition

On [`XCompiler`](../../inc-comp/IncComp/General.lean#L22) ([`General.lean`](../../inc-comp/IncComp/General.lean), section Precision): after recompiling `R`, a unit outside `R` is **necessary** ([`XCompiler.Necessary`](../../inc-comp/IncComp/General.lean#L173)) when an answer its last compilation read changed, T1's converse as a definition; it is **over-invalidated** when `inv(ΔAPI)` holds it and it is not necessary ([`XCompiler.overInvalidated`](../../inc-comp/IncComp/General.lean#L207)). Two theorems:

- [`XCompiler.necessary_invalidated`](../../inc-comp/IncComp/General.lean#L187): under the obligations, an up-to-date unit outside `R` that is necessary is invalidated. By locality a key owned outside the affected units keeps its hash; by abstraction an unchanged hash means an unchanged answer. So the necessary set is the floor every key-based bridge design shares, and over-invalidation is the whole difference between such designs.
- [`XCompiler.policyOver_mono`](../../inc-comp/IncComp/General.lean#L222): a policy that recompiles a subset of what another recompiles over-invalidates no more, round for round; [`Flat.rulePolicy_mono`](../Zinc/Bridges/FlatRules.lean#L107) instantiates it for rule sets. Across rounds the states diverge, so the loop's total is measured, not proved.

`SplitProof`'s `Necessary`, `Invalidated` and `necessary_invalidated` (phase 10) are this statement on one lift; the framework now has it once.

## The measurement

`lake exe exhaustive precision [N] [every K]` runs every preset over `FlatRules`' space and sums, per run, the classes recompiled beyond the edited one, the necessary classes ([`Flat.necessaryOf`](../Zinc/Bridges/FlatRules.lean#L345), the same for every preset), the recompiled classes that were not necessary, and the recompiled classes whose output the edit left unchanged. The presets ([`Flat.presets`](../Zinc/Bridges/FlatRules.lean#L394)) are the ones Zinc ships or the PoC plan considers: `all` (today: every descendant of a changed API, [`Rule.all`](../Zinc/Bridges/FlatRules.lean)), `strict` (the default plus `uses`), the default with `trait`, the default with `traitDirect` ([rz#30](https://github.com/retronym/zinc/issues/30)), `traitDirect` narrowed to changes that add, remove or re-abstract a member the trait implements ([`Rule.traitConcrete`](../Zinc/Bridges/FlatRules.lean), the plan's "`trait` only for concrete members"), the default without `header` with extends clauses recorded, and `none`. All of them record a class's selections of its own inherited members as `memberRef`s on the owner ([`Flat.withUses`](../Zinc/Bridges/FlatRules.lean#L391)), which is what the Scala 2 bridge does and the PoC's reason for dropping the `uses` rule; without that the default presets are the known-unsound ablation of phase 3.

### Every 23rd base (9,392 bases, 253,584 edits; `lake exe exhaustive precision every 23`)

Sums over the runs. "Recompiled" is beyond the edited class; "necessary" is the trace floor; "over-invalidated" is recompiled and not necessary; "output unchanged" is recompiled with the same output as before the edit, the coarse floor. A prime stride, since the enumeration's inner cycle is 32 and a stride of 20 never picks a base with `A` as a trait (found through the dashboard's samples).

| preset | unclean | recompiled | necessary | over-invalidated | of recompiled | output unchanged |
|---|---|---|---|---|---|---|
| all (every descendant of a changed API) | 0 | 920,193 | 565,333 | 354,860 | 38.5% | 550,534 |
| strict (default + uses) | 0 | 915,531 | 565,333 | 352,538 | 38.5% | 545,872 |
| default, trait | 0 | 915,531 | 565,333 | 352,538 | 38.5% | 545,872 |
| default, traitDirect without the class-or-object clause (the model before phase 30) | 0 | 905,923 | 565,333 | 346,344 | 38.2% | 536,264 |
| default, traitDirect narrowed to implemented members | 0 | 905,652 | 565,333 | 346,344 | 38.2% | 535,993 |
| default, traitDirect (Zinc's: classes and objects that mix the trait in) | 0 | 900,348 | 565,333 | 342,708 | 38.0% | 530,689 |
| default, traitDirect, without header (extends clauses recorded) | 0 | 896,531 | 565,333 | 346,344 | 38.6% | 526,872 |
| none (unsound) | 165,286 | 442,569 | 565,333 | 301,753 | 68.1% | 315,472 |

### The whole space (216,000 bases, 5,832,000 edits; `lake exe exhaustive precision`, about 12 CPU-hours)

With the model's `traitDirect` aligned to Zinc's. The sample's rates hold to the decimal.

| preset | unclean | recompiled | necessary | over-invalidated | of recompiled | output unchanged |
|---|---|---|---|---|---|---|
| all (every descendant of a changed API) | 0 | 21,162,880 | 13,002,688 | 8,160,192 | 38.5% | 12,662,720 |
| strict (default + uses) | 0 | 21,055,936 | 13,002,688 | 8,106,720 | 38.5% | 12,555,776 |
| default, trait | 0 | 21,055,936 | 13,002,688 | 8,106,720 | 38.5% | 12,555,776 |
| default, traitDirect without the class-or-object clause (the model before phase 30) | 0 | 20,835,136 | 13,002,688 | 7,964,256 | 38.2% | 12,334,976 |
| default, traitDirect narrowed to implemented members | 0 | 20,828,736 | 13,002,688 | 7,964,256 | 38.2% | 12,328,576 |
| default, traitDirect (Zinc's: classes and objects that mix the trait in) | 0 | 20,707,136 | 13,002,688 | 7,881,056 | 38.0% | 12,206,976 |
| default, traitDirect, without header (extends clauses recorded) | 0 | 20,491,136 | 13,002,688 | 7,881,056 | 38.4% | 11,990,976 |
| none (unsound) | 3,800,688 | 10,178,400 | 13,002,688 | 6,938,912 | 68.1% | 7,254,272 |

## What the numbers say

**The rules are worth about three percent on this space, and the floor is sixty.** Every sound preset recompiles about 3.6 classes per edit beyond the edited one, and about 60% of those have the same output after the edit as before. The spread from `all` to the best sound preset is 21,162,880 to 20,491,136, 3.2%, and to Zinc's default 2.2%. The reason is the space's shape: its clients `X`, `Y`, `Z` each select `m` on `B`, `C` or `A`, so almost every edit changes an answer they read and they are recompiled by their keys under every preset; the descendant rules decide only `B`, `C` and `X`-as-subclass, and those read their ancestors (the refchecks prelude, the forwarders) often enough that most of their recompiles are necessary by the trace. The PoC's wins come from fan-out that this space does not have: Spark's `TreeNode` has 261 descendants and a few clients per class. The *rates* per descendant transfer; the totals do not.

**Two floors.** The necessary set (an answer the class read changed) and the output-unchanged set (the edit did not change what the class compiles to) differ by a factor of about 1.5, and the sound presets sit between them: `traitDirect` recompiles 905,923, of which 559,579 are necessary by the trace, 5,754 fewer than the 565,333 necessary classes, and it is clean on every run. `lake exe exhaustive precision why` shows which answers those skipped classes read: `has m` and `dfr m`, asked of every ancestor by the conflict and abstract-member checks. The exact answer moves (`A` gains `m`, so "does `A` declare `m`" flips) while the refchecks outcome does not (`B` declares nothing, so no override, no conflict, nothing to implement). A design that recorded those queries as keys would recompile `B`; the rule table, computed on Zinc's side from stored stubs, asks the coarser question the decision needs. So the rules are more precise than the key-per-query bridge the obligations describe, and `necessary_invalidated`'s floor is a floor for key-based designs, not for policies. Against the coarse floor, `all` wastes 59.8% of its descendant recompiles and the best sound preset 58.8%.

**Which rules, and a parity gap.** `trait` against `traitDirect` as the model had it: 1.0%, the step the PoC took ([rz#30](https://github.com/retronym/zinc/issues/30)). The dashboard's second sample on the first run showed every preset recompiling trait `A extends M` with unchanged output when `M` gained a `var`: a trait that mixes a trait in gets no forwarders and implements no fields. A class-or-object clause on `traitDirect` is clean on every run of the sample and saves another 0.6%. Porting it to Zinc found it was already there: `HierarchyView.mixesIn` has begun with `!isTrait(descendant)` since retronym/zinc e1bf9d747 (9 October), so the gap was the model's, which had rendered `traitDirect` without the clause (now [`Rule.traitDirectAny`](../Zinc/Bridges/FlatRules.lean), kept for comparison), and the 0.6% is what Zinc already gains. That is slice item 2.2 (rule-table parity) in practice: the model's `traitDirect` now matches Zinc's, and the Zinc side gained the scripted test `merkle-trait-descendant-trait` (retronym/zinc branch `claude/merkle-trait-descendant-trait`, which fails with the clause removed and under `strict`). `traitConcrete` (fire only when an implemented member is added, removed or re-abstracted) buys 0.03% and is not worth a rule. Dropping `header` with extends clauses recorded: 1.0%, but it moves the `abstract`/`conflicts` reads onto the `memberRef` edge, so it depends on item 2.3 of the slice (is every descendant a `memberRef` client of its parent).

**What the space cannot say.** No library ancestor, so the coarseness of folding jar stamps into inherited names (slice item 2.4) is not counted; two descendants, so no fan-out; one name.

## For the PoC

- The sound presets agree with the `FlatRules` soundness check (0 unclean); `none` does not.
- `traitDirect` as Zinc ships it is the right default on the numbers, and now matches the model. `traitConcrete` is not worth a rule. The header rule's cost is quantified; dropping it needs the extends-clause key, which Zinc has as the `memberRef` on the parent, so the open question is only whether that edge is guaranteed (slice item 2.3).
- The dashboard (`lake exe exhaustive precision 100`, about ten seconds) prints two concrete programs per batch with every preset's recompiled set and the two floors, and with `PRECISION_LOG=file` records one JSON line per batch; it doubles as a talk demonstration, and a replay page over the log is the next step if one is wanted.
- The PR description for [rz#30](https://github.com/retronym/zinc/issues/30) can cite this table and `necessary_invalidated` as the definition it is measured against.
