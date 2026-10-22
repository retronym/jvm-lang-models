# distil-and-model: a draft skill

[SKILL.md](SKILL.md) is the method; [example.md](example.md) is one complete climb, a presentation compiler interrupted mid-check, from the real bug to a toy, kernels, a model, a conformance theorem, a space of 1,372 scenarios and patches on two real compilers. The folder is self-contained and can be copied into any project's skills directory. It is a draft: it has been exercised on one mechanism only.

## When not to use it

* **The question is about a language feature's output, not a mechanism.** What a compiler emits for a construct, or whether a type operation obeys a law, is calibration: probes against the real tool and a model of the output, with no toy in between.
* **There is only one system.** The kernels rung needs two or three designs of the same mechanism to compare; with one, the survey is a reading note and the toy is a reimplementation with no oracle but itself.
* **The source cannot be read.** Every rung above the first holds something to the real system's code at a named commit. A closed system, or one read only through documentation, gives a toy whose fidelity cannot be checked.
* **The answer is a measurement.** The toy's work counter ranks designs; it does not time them. A latency or memory question goes to a profiler on the real system.
* **The bug has a one-line fix and a test already.** The ladder costs days. It pays when the fix's completeness is in doubt, when a design is being chosen, or when the mechanism has no specification and needs one.
* **The mechanism needs what the toy would have to leave out.** If the question is about trees with positions, edits inside bodies or identity across runs, a toy of lazy facts is the wrong toy; build the next one rather than stretching this one.
