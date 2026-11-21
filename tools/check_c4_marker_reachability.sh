#!/usr/bin/env bash
# Run canonical regressions, compare both runtimes, and export replayable evidence.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd -P)
mkdir -p "${1:?pass an output directory for the replay evidence}"
out=$(cd "$1" && pwd -P)

cd "$root/kernel"
pixi run --locked mojo build -I . -I tests tests/test_c4_marker_reachability.mojo -o "$out/marker-tests"
pixi run --locked mojo build -I . c4_marker_reachability.mojo -o "$out/marker"
"$out/marker-tests" | tee "$out/mojo-tests.txt"
"$out/marker-tests" --trace > "$out/mojo-trace.txt"

"$out/marker" 021001112220/1201100002221/0100011122221 00 00 11 right > "$out/family.tsv"
"$out/marker" 021000011111222220/1201111000000222221/0100000111112222221 00 00 11 right > "$out/family-6.tsv"
"$out/marker" 012001112220/1201100002221/0100011122221 00 00 11 right > "$out/reordered-right.tsv"
"$out/marker" 012001112220/1201100002221/0100011122221 00 00 11 left > "$out/reordered-left.tsv"
"$out/marker" 01/112/021 10 10 21 right > "$out/cycling.tsv"
"$out/marker" 01/10 00 00 11 > "$out/thue-morse.tsv"
"$out/marker" 0110/1001 00 00 11 > "$out/thue-morse-squared.tsv"
"$out/marker" check "$out/thue-morse.tsv"
"$out/marker" check "$out/thue-morse-squared.tsv"
python3 "$root/oracles/python/c4_marker_reachability.py" \
    "$out/family.tsv" "$out/family-6.tsv" "$out/reordered-right.tsv" "$out/reordered-left.tsv" \
    "$out/cycling.tsv" "$out/thue-morse.tsv" "$out/thue-morse-squared.tsv" | tee "$out/literal-replay.txt"

cd "$root/proof/PscVerif"
lake build PscVerif.PeriodicPartnerMarkerReachability PscVerif.PeriodicPartnerMarkerFamily
lake env lean --run MarkerReachabilityReplay.lean > "$out/lean-trace.txt"
diff -u "$out/lean-trace.txt" "$out/mojo-trace.txt"
printf 'Matching Mojo/Lean register rows: %s\n' "$(wc -l < "$out/mojo-trace.txt")"
