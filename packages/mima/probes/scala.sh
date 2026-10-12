#!/usr/bin/env bash
# MiMa on the Scala catalogue (packages/scala/Scala/Catalogue.lean): writes each case's library sources, compiles
# v0 and v1 separately in one compile server (packages/harness/scripts/compiler.py), and runs MiMa on the two
# class directories. With a Scala 2 version, the Scala 3 cases (enums, inline) do not compile; they are reported
# and skipped.
# Usage: packages/mima/probes/scala.sh OUT [scala-version]   (run from the repository root)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1
sv=${2:-2.13.18}
mkdir -p "$out"
lake exe bincompat scala "$out" > "$out/cases.tsv"
args=()
while read -r name; do
  for v in v0 v1; do
    args+=("$out/$name/$v.scala" "$out/$name/$v")
  done
done < <(cut -f1 "$out/cases.tsv")
failed=$(python3 -I "$here/../../harness/scripts/compiler.py" scala "$sv" "${args[@]}" || true)
cases=()
while read -r name; do
  if grep -q "^failed $out/$name/" <<< "$failed"; then
    echo "scalac $sv: $name does not compile, skipped" >&2
  else
    cases+=("$name")
  fi
done < <(cut -f1 "$out/cases.tsv")
scala-cli run --server=false "$here/Mima.scala" -- "$out" "${cases[@]}"
