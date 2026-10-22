#!/bin/sh
# Compiles the toy presentation compilers and runs every scenario under every kernel.
#   run.sh [--all] [--trace] [--sessions | --tiers] [--kernel name]...
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${TMPDIR:-/tmp}/pctoy-classes
mkdir -p "$OUT"
javac --release 21 -d "$OUT" "$HERE"/src/pctoy/*.java
java -cp "$OUT" pctoy.Main "$HERE/scenarios" "$@"
