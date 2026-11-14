#!/usr/bin/env bash
# Compile the family and its complete dependency closure from isolated sources.
# Local .olean files and Lake configuration are never copied into this gate.
set -euo pipefail
PSC_FAMILY_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_FAMILY_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_FAMILY_TMP"' EXIT
python3 "$PSC_FAMILY_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_FAMILY_TMP/proof/PscVerif"
for PSC_FAMILY_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_FAMILY_ENV" ]]; then unset "$PSC_FAMILY_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export MATHLIB_CACHE_DIR="$PSC_FAMILY_TMP/download-cache"
export MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4-master"
cd "$PSC_FAMILY_TMP/proof/PscVerif"
PSC_FAMILY_PIN=$(cat lean-toolchain)
PSC_FAMILY_RELEASE=${PSC_FAMILY_PIN#leanprover/lean4:v}
PSC_FAMILY_LEAN_VERSION=$(elan run "$PSC_FAMILY_PIN" lean --version)
PSC_FAMILY_LAKE_VERSION=$(elan run "$PSC_FAMILY_PIN" lake --version)
if [[ "$PSC_FAMILY_LEAN_VERSION" != "Lean (version $PSC_FAMILY_RELEASE,"* ]] \
   || [[ "$PSC_FAMILY_LAKE_VERSION" != *"(Lean version $PSC_FAMILY_RELEASE)" ]]; then
    echo "Lean/Lake executable version does not match the pinned release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_FAMILY_LEAN_VERSION" "$PSC_FAMILY_LAKE_VERSION"
psc_family_check_pins() {
    for PSC_FAMILY_CONFIG in lean-toolchain lakefile.toml lake-manifest.json; do
        cmp "$PSC_FAMILY_ROOT/proof/PscVerif/$PSC_FAMILY_CONFIG" "$PSC_FAMILY_CONFIG"
    done
    python3 - "$PSC_FAMILY_ROOT" "$PSC_FAMILY_TMP" <<'PY'
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / "tools"))
from make_proof_bank import check_pins
check_pins(pathlib.Path(sys.argv[2]), require_packages=True)
PY
}
elan run "$PSC_FAMILY_PIN" lake --no-cache env true
psc_family_check_pins
elan run "$PSC_FAMILY_PIN" lake --no-cache exe cache get
elan run "$PSC_FAMILY_PIN" lake --no-cache build \
    PscVerif.C4ParameterFamilyBridge PscVerif.C4ParameterFamilyControls \
    PscVerif.UniversalClosureReduction
psc_family_check_pins
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean C4ParameterFamilyAudit.lean \
    | tee "$PSC_FAMILY_TMP/family-audit.log"
test "$(grep -c '^PSC_PARAMETER_FAMILY_ENDPOINT' "$PSC_FAMILY_TMP/family-audit.log")" -eq 11
for PSC_FAMILY_ENDPOINT in \
    Psc.ParameterFamily.finite_and_productive \
    Psc.ParameterFamily.coincidence_child \
    Psc.ParameterFamily.terminates_with_coincidence \
    Psc.ParameterFamilyPisot.primitive \
    Psc.ParameterFamilyPisot.irreducible \
    Psc.ParameterFamilyPisot.pisot \
    Psc.TerminationFactors.terminates_iff_finite_factors_and_coincidences \
    Psc.ParameterFamilyBridge.full_factor_termination \
    Psc.ParameterFamilyBridge.spectral_criterion_inputs \
    Psc.UniversalClosureReduction.all_blocks_productive \
    Psc.UniversalClosureReduction.infinite_seed_reachability; do
    test "$(awk -F '\t' -v name="$PSC_FAMILY_ENDPOINT" \
        '$1 == "PSC_PARAMETER_FAMILY_ENDPOINT" && $2 == name {n++} END {print n+0}' \
        "$PSC_FAMILY_TMP/family-audit.log")" -eq 1
done
test "$(grep -c '^PSC_PARAMETER_FAMILY_MODULE' "$PSC_FAMILY_TMP/family-audit.log")" -eq 8
test "$(awk -F '\t' '$1 == "PSC_PARAMETER_FAMILY_DECLARATIONS" && $2 == 8 {n++} END {print n+0}' \
    "$PSC_FAMILY_TMP/family-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_PARAMETER_FAMILY_AUDIT_COMPLETE\t11\t22' "$PSC_FAMILY_TMP/family-audit.log")" -eq 1
psc_family_check_pins
