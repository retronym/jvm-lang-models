#!/usr/bin/env bash
# Renders the catalogue with the Classfile API (JDK 24+) and runs it on every JDK given.
# Usage: packages/jvm/probes/probe.sh [catalogue|space|chain|cases.jsonl] -- JAVA_HOME...   (run from the repository root)
# A space name is dumped with `lake exe jvmcases <name>` (`catalogue`, the default, is plain `jvmcases`).
# With OUT=dir, the rendered classfiles are kept in dir/<case>/{v0,v1,client,sites} (for MiMa, Track B).
# With RUNS=ledger.jsonl, the run is appended to the ledger as one JSON line, and the per-program
# verdicts are kept beside it in verdicts/ (see runs/README.md).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
arg=catalogue
if [ -n "${1:-}" ] && [ "$1" != "--" ]; then arg=$1; shift; fi
[ "${1:-}" = "--" ] && shift
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
out=${OUT:-$work/out}
case "$arg" in
  catalogue) space=catalogue; cases=$work/cases.jsonl; lake exe jvmcases > "$cases" ;;
  space|chain) space=$arg; cases=$work/cases.jsonl; lake exe jvmcases "$arg" > "$cases" ;;
  *) space=$(basename "$arg" .jsonl); cases=$arg ;;
esac
commit=$(git rev-parse HEAD)
dirty=false; git diff --quiet HEAD -- . ':(exclude)packages/*/probes/runs' || dirty=true
render=${RENDER_JAVA_HOME:-$HOME/.sdkman/candidates/java/25.0.4-tem}
"$render/bin/javac" -d "$work/render" "$here/Render.java" "$here/Json.java"
"$render/bin/java" -cp "$work/render" Render "$cases" "$out"
"$render/bin/javac" --release 17 -d "$work/run" "$here/Run.java" "$here/Json.java" "$here/ProbeLog.java"
status=0
i=0
for jh in "$@"; do
  "$jh/bin/java" -cp "$work/run" Run "$cases" "$out" > "$work/run-$i.tsv" || status=1
  grep -v '^#json ' "$work/run-$i.tsv"
  i=$((i + 1))
done
if [ -n "${RUNS:-}" ]; then
  date=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  mkdir -p "$(dirname "$RUNS")/verdicts"
  verdicts=verdicts/${date%%T*}-$space-${commit:0:10}.tsv.gz
  jdks=
  for ((j = 0; j < i; j++)); do
    summary=$(sed -n 's/^#json //p' "$work/run-$j.tsv")
    jdks=$jdks${jdks:+,}$summary
    jdk=$(printf %s "$summary" | sed 's/.*"jdk":"\([^"]*\)".*/\1/')
    grep -v '^#' "$work/run-$j.tsv" | sed "s/^/$jdk\t/" >> "$work/verdicts.tsv"
  done
  gzip -n < "$work/verdicts.tsv" > "$(dirname "$RUNS")/$verdicts"
  printf '{"date":"%s","commit":"%s","dirty":%s,"space":"%s","programs":%s,"jdks":[%s],"verdicts":"%s"}\n' \
    "$date" "$commit" "$dirty" "$space" "$(grep -c . "$cases")" "$jdks" "$verdicts" >> "$RUNS"
fi
exit $status
