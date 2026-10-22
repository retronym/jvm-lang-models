# distil-and-model: a draft skill

[`SKILL.md`](SKILL.md) encapsulates the method of [`docs/method.md`](../../method.md). It is a draft: it has not been exercised on a track other than the one it was written from, and it is kept here so that it can be read beside the method page before anyone enables it.

## When not to use it

* **The question is about a language feature, not a mechanism.** What scalac emits for a `lazy val`, or whether a join is commutative, is a calibration track ([`track-s.md`](../../../packages/scala/docs/track-s.md), [`track-lub.md`](../../../packages/scala-types/docs/track-lub.md)): probes against the real compiler and a model of the output, with no toy in between.
* **There is only one system.** The kernels rung needs two or three designs of the same mechanism to compare; with one, the survey is a reading note and the toy is a reimplementation with no oracle but itself.
* **The source cannot be read.** Every rung above the first holds something to the real system's code at a named commit. A closed system, or one read only through documentation, gives a toy whose fidelity cannot be checked.
* **The answer is a measurement.** The toy's work counter ranks designs; it does not time them. A latency or memory question goes to a profiler on the real system.
* **The bug has a one-line fix and a test already.** The ladder costs days. It pays when the fix's completeness is in doubt, when a design is being chosen, or when the mechanism has no specification and needs one.
* **The mechanism needs what the toy would have to leave out.** Trees with positions, edits inside bodies, identity across runs: if the question is about those, the toy of Track I is the wrong toy, and the next one is a future-work item in [`track-i.md`](../../../packages/scala/docs/track-i.md), not this skill.
