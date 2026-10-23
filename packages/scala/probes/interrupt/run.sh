#!/bin/sh
# Compiles the toy presentation compilers and runs every scenario under every kernel.
#   run.sh [--all] [--trace] [--sessions | --tiers | --concurrent] [--kernel name]...
# `--concurrent` runs the two-reader scenarios (`concurrent-*.toy`) on the concurrent kernels, every pair of safepoints.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${TMPDIR:-/tmp}/pctoy-classes
mkdir -p "$OUT"
javac --release 21 -d "$OUT" "$HERE"/src/pctoy/*.java
java -cp "$OUT" pctoy.Main "$HERE/scenarios" "$@"
