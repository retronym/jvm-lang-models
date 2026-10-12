# `Links`

Theorems that connect layers. B4 (`untouched_eq_clean`): for a front end meeting Zinc's obligations, a unit Zinc never recompiles equals the clean build's, so it links as a fresh build does; Zinc-clean implies binary-compatible, and the converse fails (the gap is what MiMa reports).

**Start here.** [`Links/ZincBridge.lean`](Links/ZincBridge.lean).

**Calibration.** Through `scala` and `jvm`, which are calibrated.

**Gaps.** The explicit-interface T3 that B4 needs is restated here for `XCompiler`; it belongs in `inc-comp`.

## Files

| File | Contents |
|---|---|
| [`ZincBridge.lean`](Links/ZincBridge.lean) | Scala lowering as an `XCompiler`; T3b (explicit) for `XCompiler`; B4 `untouched_eq_clean` |
| [`ZincBridgeKeys.lean`](Links/ZincBridgeKeys.lean) | B4 with Zinc's actual keys (inheritance, member refs): `loop_witness` ([retronym/zinc#57](https://github.com/retronym/zinc/issues/57)) |
| [`ZincBridgeLibs.lean`](Links/ZincBridgeLibs.lean) | B4 for a client of a library JAR (stamp keys) |
| [`ZincBridgeScala3.lean`](Links/ZincBridgeScala3.lean) | B4 for Scala 3: `comp` fails under F6 (`not_comp`) and holds with [retronym/scala3#10](https://github.com/retronym/scala3/issues/10) (`after_eq_fresh_fix`) |
