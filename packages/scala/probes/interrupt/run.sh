#!/bin/sh
# Compiles the toy presentation compilers and runs every scenario under every kernel.
#   run.sh [--all] [--trace] [--sessions | --tiers | --concurrent] [--kernel name]...
# `--concurrent` runs the two-reader scenarios (`concurrent-*.toy`) on the concurrent kernels, every pair of safepoints;
# a scenario with `// cancel: A` also cancels the first reader at each of its safepoints, for every pair. The kernels
# (ConcurrentHarness.KERNELS) vary the peek (`isCompleting` on either reader or on this one), the per-reader scratch,
# the root a completion claims and other readers wait on (a fact, a class with its companion as the symbol loader has
# it, a file as TASTy has it: design §3.1 "Groups"), what the reader closing a wait-for cycle does (RAISE a
# CyclicReference, §4.2 as written; or be the VICTIM, aborted and retried, the implementation's rule, I74), and whether
# a file root's reading sentinel (TASTy's PoisonTree in treeAtAddr) is cleared on an unwind (`-leak`: not, as
# TreeUnpickler.readIndexedDef has it). The report counts, per kernel, races, cycles reported at another site, false
# cycles (a cyclic reference the sequential run does not have: I54, I87), deadlocks, victim aborts and retry bounds hit.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${TMPDIR:-/tmp}/pctoy-classes
mkdir -p "$OUT"
javac --release 21 -d "$OUT" "$HERE"/src/pctoy/*.java
java -cp "$OUT" pctoy.Main "$HERE/scenarios" "$@"
