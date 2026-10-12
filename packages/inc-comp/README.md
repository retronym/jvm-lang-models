# `IncComp`

When does an incremental build equal a clean one, for any compiler and any invalidation policy? A compiler is a per-unit `Task` plus a bridge (`keys`, `π`, `covers`); the obligations on it are compositionality, coverage and abstraction (and locality for non-local hashes); a policy must never drop an invalidated unit. The general form [`XCompiler`](IncComp/General.lean#L20) proves T2, T3a, T4 (monotone policies) and T5 once; the local `Compiler` and the variants [`TCompiler`](IncComp/Tree.lean#L24), [`GCompiler`](IncComp/NonLocal.lean#L25), [`NCompiler`](IncComp/NonLocalAns.lean#L32) are defined through their lift `toX`. Nothing here is specific to Zinc.

**Start here.** [`IncComp/Model.lean`](IncComp/Model.lean) (the first page of the specification), then [`IncComp/General.lean`](IncComp/General.lean). The statements are in the root README's theorem table.

**Calibration.** The instances in `zinc` and the harness calibrate it against real Zinc.

**Gaps.** T3 (incremental = clean) needs hypotheses real Scala does not meet (root README, "Where the hypotheses bite"); precision has no framework definition yet.

## Files

| File | Contents |
|---|---|
| `Model.lean` | `Compiler` (task, joint compiler, `iface`, `answer`, `π`, `keys`, `covers`), its three `Obligations`, `State`, `round`, `invalidated`, `Policy` and [`Policy.Sound`](IncComp/Model.lean#L117), the fuelled `zinc` loop |
| [`General.lean`](IncComp/General.lean) | [`XCompiler`](IncComp/General.lean#L20), the general form: non-local answers and hashes, keys from output and trace; T2, T3a, T4 (monotone), T5a, T5 and snapshot refresh, proved once |
| [`Soundness.lean`](IncComp/Soundness.lean) | `UpToDate` and `Inv` for `Compiler`; T2 and T3a through the lift `toX` (`zinc_toX`) |
| [`Uniqueness.lean`](IncComp/Uniqueness.lean) | T3b [`fixpoint_unique_of_wf`](IncComp/Uniqueness.lean#L64), `_of_explicit`; T3 `zinc_eq_clean_of_*`, for `Compiler` and [`TCompiler`](IncComp/Tree.lean#L24) |
| [`Termination.lean`](IncComp/Termination.lean) | T4: monotone policies, explicit interfaces (2 rounds), acyclic (height + 2) |
| [`NonLocal.lean`](IncComp/NonLocal.lean) | [`GCompiler`](IncComp/NonLocal.lean#L25): non-local `π` with `hashDeps`, closure keys, `Δ` over `affected`; T2′ through `toX` |
| [`NonLocalAns.lean`](IncComp/NonLocalAns.lean) | [`NCompiler`](IncComp/NonLocalAns.lean#L32): answers and hash read sets over several interfaces; T2″, T3a″ through `toX` |
| [`Tree.lean`](IncComp/Tree.lean) | [`TCompiler`](IncComp/Tree.lean#L24): keys read off the output (the typed tree), not the trace; T2, T3a through `toX` |
| [`Classpath.lean`](IncComp/Classpath.lean) | Upstream subprojects and libraries: stored snapshots, external invalidation; T5a, T5 |
| [`Stale.lean`](IncComp/Stale.lean) | T2-stale: [`stale_unsound`](IncComp/Stale.lean#L130), [`stale_affected`](IncComp/Stale.lean#L135), [`stale_none_invalidated`](IncComp/Stale.lean#L127), [`stale_repaired`](IncComp/Stale.lean#L139), by kernel `decide` |
