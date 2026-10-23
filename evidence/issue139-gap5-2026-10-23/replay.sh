#!/usr/bin/env bash
# Replay exact sources in a full lock-managed Pixi environment.
set -euo pipefail
cd "$(dirname "$0")/../.."
E=evidence/issue139-gap5-2026-10-23
(cd "$E" && sha256sum -c SHA256SUMS)
mkdir -p kernel/build/gap-five
cd kernel
pixi run --locked mojo build -I . class_c_gap_five.mojo -o build/gap-five/c
pixi run --locked mojo build -I . class_a_gap_five_probe.mojo -o build/gap-five/a
pixi run --locked mojo build -I . tests/test_gap_five_domains.mojo -o build/gap-five/domains
build/gap-five/domains > build/gap-five/domains.log
for side in plus minus; do
  eps=1
  if [[ $side == minus ]]; then eps=-1; fi
  timeout 300 build/gap-five/a "$eps" > "build/gap-five/a-$side.log"
  diff "../$E/a-$side.log" "build/gap-five/a-$side.log"
  timeout 1200 build/gap-five/c "$eps" > "build/gap-five/c-$side.log"
  diff "../$E/c-$side.log" "build/gap-five/c-$side.log"
done
diff "../$E/domains.log" build/gap-five/domains.log
