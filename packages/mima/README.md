# `MiMa`

Which library edits MiMa reports, which it misses, and corrected rules. MiMa (`mima-core` 1.2.1's `Analyzer`) modelled as a bridge design over `jvm`: its keys, what they cover, and its gaps as missed footprint queries.

**Start here.** `MiMa/Keys.lean`.

**Calibration.** `probes/` runs MiMa on the rendered cases and compares: five gaps (MiMa-F1, M1, F2, D1, P1), 40 false negatives on the edit space. `docs/PLAN-track-b.md`.

**Gaps.** `MiMa/Sound.lean` checks the corrected rules on the edit space only; a proof for every library is open. 17 `ReversedMissingMethodProblem` reports need method bodies (Track J4).

`MiMa/Sound.lean` is outside the default target: `lake build MiMa.Sound` (about half an hour).

## Files

| File | Contents |
|---|---|
| `Mima.lean` | `mima-core` 1.2.1's `Analyzer` as a function of the old and new classfiles |
| `Edits.lean` | The space of single library edits, and their clients |
| `Keys.lean` | MiMa as a bridge design: keys, covering, and its gaps as missed footprint queries |
| `Fixed.lean` | A corrected rule set, one key per gap |
| `Sound.lean` | The corrected rules are sound on the space (kernel `decide`; built on demand) |
| `probes/` | `Mima.scala` runs MiMa on rendered cases, `scala.sh` on the Scala catalogue, `compare.py` diffs MiMa against the model |
