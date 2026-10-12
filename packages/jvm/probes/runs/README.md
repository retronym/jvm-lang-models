# Calibration ledger

One JSON line per HotSpot probe run in [`ledger.jsonl`](ledger.jsonl), appended by [`probe.sh`](../probe.sh) when `RUNS` names it:

```bash
RUNS=packages/jvm/probes/runs/ledger.jsonl packages/jvm/probes/probe.sh chain -- $JDK21 $JDK25 $JDK27
```

A track document that quotes a calibration result cites the line it comes from, so it says when the result was last true and against which commit.

Fields:

- `date`: when the run finished, UTC.
- `commit`: the repository's `HEAD` when the run started; `dirty` is true if the working tree then differed from it outside this directory, in which case the line records a run of uncommitted model code.
- `space`: what was run: `catalogue` (`lake exe jvmcases`), `space` (every catalogue case over its client space), `chain` (Track J6's `chainSpace`), or the basename of a cases file.
- `programs`: the cases in the dump; each is run against `v0` and `v1`.
- `jdks`: per JDK, the `java.vm.version`, the cases run, the `DISAGREE` count, and the known deviations by bug (JDK-8356942, JDK-8350029; see [`track-j.md`](../../docs/track-j.md)), counted per world.
- `verdicts`: the per-program verdicts, gzipped TSV in `verdicts/`: JDK, case, world, model outcome, JVM outcome, verdict, JVM message. The model column is the model's prediction at `commit`, so a model change that alters a prediction on a calibrated space shows as a diff of that column against a fresh `lake exe jvmcases` dump.
