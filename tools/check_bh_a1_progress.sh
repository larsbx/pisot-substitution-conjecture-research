#!/usr/bin/env bash
# Source-isolated verification of the conditional BH bridge and A1 tail words.
# Project objects and caller Lake configuration are never copied into this gate.
set -euo pipefail
PSC_PROGRESS_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_PROGRESS_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_PROGRESS_TMP"' EXIT
python3 "$PSC_PROGRESS_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_PROGRESS_TMP/proof/PscVerif"
for PSC_PROGRESS_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_PROGRESS_ENV" ]]; then unset "$PSC_PROGRESS_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export MATHLIB_CACHE_DIR="$PSC_PROGRESS_TMP/download-cache"
export MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4-master"
cd "$PSC_PROGRESS_TMP/proof/PscVerif"
PSC_PROGRESS_PIN=$(cat lean-toolchain)
PSC_PROGRESS_RELEASE=${PSC_PROGRESS_PIN#leanprover/lean4:v}
PSC_PROGRESS_LEAN_VERSION=$(elan run "$PSC_PROGRESS_PIN" lean --version)
PSC_PROGRESS_LAKE_VERSION=$(elan run "$PSC_PROGRESS_PIN" lake --version)
if [[ "$PSC_PROGRESS_LEAN_VERSION" != "Lean (version $PSC_PROGRESS_RELEASE,"* ]] \
   || [[ "$PSC_PROGRESS_LAKE_VERSION" != *"(Lean version $PSC_PROGRESS_RELEASE)" ]]; then
    echo "Lean/Lake executable version does not match the pinned release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_PROGRESS_LEAN_VERSION" "$PSC_PROGRESS_LAKE_VERSION"
psc_progress_check_pins() {
    for PSC_PROGRESS_CONFIG in lean-toolchain lakefile.toml lake-manifest.json; do
        cmp "$PSC_PROGRESS_ROOT/proof/PscVerif/$PSC_PROGRESS_CONFIG" "$PSC_PROGRESS_CONFIG"
    done
    python3 - "$PSC_PROGRESS_ROOT" "$PSC_PROGRESS_TMP" <<'PY'
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / "tools"))
from make_proof_bank import check_pins
check_pins(pathlib.Path(sys.argv[2]), require_packages=True)
PY
}
psc_progress_check_endpoints() {
    local log=$1 prefix=$2 modules=$3
    shift 3
    local count=$# endpoint
    test "$(grep -c "^${prefix}_ENDPOINT" "$log")" -eq "$count"
    for endpoint in "$@"; do
        test "$(awk -F '\t' -v marker="${prefix}_ENDPOINT" -v name="$endpoint" \
            '$1 == marker && $2 == name {n++} END {print n+0}' "$log")" -eq 1
    done
    test "$(grep -c "^${prefix}_MODULE" "$log")" -eq "$modules"
    test "$(awk -F '\t' -v marker="${prefix}_DECLARATIONS" -v modules="$modules" \
        '$1 == marker && $2 == modules {n++} END {print n+0}' "$log")" -eq 1
    local completion
    printf -v completion '%s_AUDIT_COMPLETE\t%d\t%d' "$prefix" "$count" "$((2 * count))"
    test "$(grep -Fxc "$completion" "$log")" -eq 1
}
elan run "$PSC_PROGRESS_PIN" lake --no-cache env true
psc_progress_check_pins
elan run "$PSC_PROGRESS_PIN" lake --no-cache exe cache get
elan run "$PSC_PROGRESS_PIN" lake --no-cache build \
    PscVerif.BHFiniteCarrier PscVerif.A1PrimeTailPisot
psc_progress_check_pins
elan run "$PSC_PROGRESS_PIN" lake --no-cache env lean BHFiniteReachabilityAudit.lean \
    | tee "$PSC_PROGRESS_TMP/bh-audit.log"
psc_progress_check_endpoints "$PSC_PROGRESS_TMP/bh-audit.log" PSC_BH_FINITE 3 \
    Psc.BHFiniteReachability.packet_path_tileCut \
    Psc.BHFiniteReachability.TileCut.pad \
    Psc.BHFiniteReachability.uniform_tileCut_depth \
    Psc.BHFiniteReachability.factor_bound_of_tileCuts \
    Psc.BHFiniteReachability.finite_balanced_pairs_of_physical_bound \
    Psc.BHFiniteReachability.bounded_late_factors_of_finite_packet_hits \
    Psc.BHFiniteReachability.finite_factors_of_finite_packet_hits \
    Psc.BHFiniteReachability.finite_reachable_of_finite_packet_hits \
    Psc.BHFiniteReachability.physical_zero_does_not_supply_tileCut \
    Psc.OccurrenceAncestry.covers_iterates_of_closed \
    Psc.BHFiniteCarrier.finite_reachable_of_closed_packet_cover
elan run "$PSC_PROGRESS_PIN" lake --no-cache env lean A1PrimeTailAudit.lean \
    | tee "$PSC_PROGRESS_TMP/a1-audit.log"
psc_progress_check_endpoints "$PSC_PROGRESS_TMP/a1-audit.log" PSC_A1_TAIL 2 \
    Psc.A1PrimeTailCoincidence.six_level_coincidence \
    Psc.A1PrimeTailPisot.primitive \
    Psc.A1PrimeTailPisot.irreducible \
    Psc.A1PrimeTailPisot.pisot \
    Psc.A1PrimeTailCoincidence.second_layer_six_level \
    Psc.A1PrimeTailPisot.second_primitive \
    Psc.A1PrimeTailPisot.second_irreducible \
    Psc.A1PrimeTailPisot.second_pisot \
    Psc.A1PrimeTailCoincidence.z4_three_level \
    Psc.A1PrimeTailPisot.third_layer_unit_root \
    Psc.A1PrimeTailCoincidence.residual_parameter_cases \
    Psc.A1PrimeTailPisot.residual_run_split \
    Psc.A1PrimeTailCoincidence.first_layer_simultaneous \
    Psc.A1PrimeTailCoincidence.second_layer_simultaneous \
    Psc.A1PrimeTailCoincidence.z4_simultaneous
psc_progress_check_pins
