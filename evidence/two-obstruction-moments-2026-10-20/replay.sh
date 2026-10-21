#!/usr/bin/env bash
# Fresh output directory required; committed receipts are never overwritten.
set -euo pipefail
repo=$(cd "$(dirname "$0")/../.." && pwd)
out=${1:?supply a new output directory}
mkdir "$out"
out=$(cd "$out" && pwd)
cd "$repo/kernel"
if [[ -n ${PSC_MOJO_RUNTIME_ROOT:-} ]]; then
  export MODULAR_MOJO_MAX_PACKAGE_ROOT="$PSC_MOJO_RUNTIME_ROOT"
  export MODULAR_MAX_PACKAGE_ROOT="$PSC_MOJO_RUNTIME_ROOT"
  export MODULAR_MOJO_MAX_IMPORT_PATH="$PSC_MOJO_RUNTIME_ROOT/lib/mojo"
  compiler=("$PSC_MOJO_RUNTIME_ROOT/bin/mojo")
else
  compiler=(pixi run --locked mojo)
fi
"${compiler[@]}" --version > "$out/version.log" 2>&1
date -u +%FT%TZ > "$out/started"
set +e
"${compiler[@]}" build -I . tests/test_length_moments.mojo -o "$out/test" > "$out/build.log" 2>&1
code=$?
echo "$code" > "$out/build.exit"
if [[ $code == 0 ]]; then
  "$out/test" > "$out/replay.log" 2>&1
  code=$?
  echo "$code" > "$out/replay.exit"
fi
date -u +%FT%TZ > "$out/finished"
exit "$code"
