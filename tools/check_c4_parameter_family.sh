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
    PscVerif.C4ParameterFamilySolenoid PscVerif.C4ParameterFamilyControls \
    PscVerif.UniversalClosureReduction PscVerif.PeriodicPartnerRealizationModels \
    PscVerif.C4ParameterFamilyZeroFibreWitnesses \
    PscVerif.C4ParameterFamilyZeroFibreControls PscVerif.C4ParameterFamilyInteriorZero \
    PscVerif.C4FiniteTileAutomaton PscVerif.C4FamilyTileAutomatonWords \
    PscVerif.C4FamilyTileAutomatonHull PscVerif.C4FamilyFiniteZeroFibre \
    PscVerif.C4FamilyFiniteProximal PscVerif.C4ParameterFamilyFibreDistal \
    PscVerif.C4FamilyOpenSynchronization PscVerif.C4FamilySolenoidCharacters \
    PscVerif.C4FamilyCharacterOrbits
psc_family_check_pins
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true C4ParameterFamilyAudit.lean \
    | tee "$PSC_FAMILY_TMP/family-audit.log"
test "$(grep -c '^PSC_PARAMETER_FAMILY_ENDPOINT' "$PSC_FAMILY_TMP/family-audit.log")" -eq 35
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
    Psc.ParameterFamilyTiling.geometry_image \
    Psc.ParameterFamilyTiling.fixed_hull_tiling \
    Psc.ParameterFamilyTiling.continuous_action \
    Psc.ParameterFamilyTiling.action_aperiodic \
    Psc.ParameterFamilyTiling.finite_local_complexity \
    Psc.ParameterFamilyTiling.swap_rotation_irrational \
    Psc.ParameterFamilyTiling.swap_rotation_dense \
    Psc.ParameterFamilyTiling.dense_swap_coincidences \
    Psc.ParameterFamilyTiling.periodic_swap_geometry \
    Psc.ParameterFamilyTiling.legal_patches_dense_eventual \
    Psc.ParameterFamilyTiling.hull_dense_eventual \
    Psc.ParameterFamilyTiling.periodic_common_tile_of_origin_witnesses \
    Psc.ParameterFamilyTiling.periodic_fibre_common_tiles \
    Psc.ParameterFamilyRecognizability.inflateH_bijective \
    Psc.ParameterFamilySolenoid.mat_eq \
    Psc.ParameterFamilySolenoid.continuous_solenoidRealize \
    Psc.ParameterFamilySolenoid.solenoidRealize_surjective \
    Psc.ParameterFamilySolenoid.solenoidRealize_finite_fibres \
    Psc.ParameterFamilySolenoid.solenoidRealize_inflate \
    Psc.ParameterFamilySolenoid.solenoidRealize_translate \
    Psc.ParameterFamilySolenoid.fixed_tiling_over_zero \
    Psc.ParameterFamilySolenoid.periodic_of_realize_zero \
    Psc.ParameterFamilySolenoid.solenoidRealize_fibres_eq_of_equivariant \
    Psc.ParameterFamilySolenoid.common_tile_of_zero_fibre_witnesses \
    Psc.UniversalClosureReduction.all_blocks_productive \
    Psc.UniversalClosureReduction.infinite_seed_reachability; do
    test "$(awk -F '\t' -v name="$PSC_FAMILY_ENDPOINT" \
        '$1 == "PSC_PARAMETER_FAMILY_ENDPOINT" && $2 == name {n++} END {print n+0}' \
        "$PSC_FAMILY_TMP/family-audit.log")" -eq 1
done
test "$(grep -c '^PSC_PARAMETER_FAMILY_MODULE' "$PSC_FAMILY_TMP/family-audit.log")" -eq 23
test "$(awk -F '\t' '$1 == "PSC_PARAMETER_FAMILY_DECLARATIONS" && $2 == 23 {n++} END {print n+0}' \
    "$PSC_FAMILY_TMP/family-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_PARAMETER_FAMILY_AUDIT_COMPLETE\t35\t70' "$PSC_FAMILY_TMP/family-audit.log")" -eq 1
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true C4ZeroFibreWitnessAudit.lean \
    | tee "$PSC_FAMILY_TMP/zero-fibre-audit.log"
test "$(grep -c '^PSC_ZERO_FIBRE_ENDPOINT' "$PSC_FAMILY_TMP/zero-fibre-audit.log")" -eq 38
test "$(grep -c '^PSC_ZERO_FIBRE_MODULE' "$PSC_FAMILY_TMP/zero-fibre-audit.log")" -eq 7
test "$(grep -Fxc $'PSC_ZERO_FIBRE_DECLARATIONS\t7\t49\t45' "$PSC_FAMILY_TMP/zero-fibre-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_ZERO_FIBRE_AUDIT_COMPLETE\t38\t76' "$PSC_FAMILY_TMP/zero-fibre-audit.log")" -eq 1
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true C4FiniteTileAutomatonAudit.lean \
    | tee "$PSC_FAMILY_TMP/finite-tile-audit.log"
test "$(grep -Fxc $'PSC_FINITE_TILE_AUDIT_COMPLETE\t164\t103' "$PSC_FAMILY_TMP/finite-tile-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_FINITE_TILE_REFUSAL_CONTROLS\t20' "$PSC_FAMILY_TMP/finite-tile-audit.log")" -eq 1
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true C4FiniteHullWitnessAudit.lean \
    | tee "$PSC_FAMILY_TMP/finite-hull-audit.log"
test "$(grep -Fxc $'PSC_FINITE_HULL_AUDIT_COMPLETE\t26\t25' "$PSC_FAMILY_TMP/finite-hull-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_FINITE_HULL_REFUSAL_CONTROLS\t48' "$PSC_FAMILY_TMP/finite-hull-audit.log")" -eq 1
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true C4FiniteProximalAudit.lean \
    | tee "$PSC_FAMILY_TMP/finite-proximal-audit.log"
test "$(grep -Fxc $'PSC_FINITE_PROXIMAL_DECLARATIONS\t9\t50\t45' "$PSC_FAMILY_TMP/finite-proximal-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_FINITE_PROXIMAL_AUDIT_COMPLETE\t44\t88' "$PSC_FAMILY_TMP/finite-proximal-audit.log")" -eq 1
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true C4FiniteSynchronizationAudit.lean \
    | tee "$PSC_FAMILY_TMP/finite-synchronization-audit.log"
test "$(grep -Fxc $'PSC_FINITE_SYNC_AUDIT_COMPLETE\t14\t14' "$PSC_FAMILY_TMP/finite-synchronization-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_FINITE_SYNC_REFUSAL_CONTROLS\t34' "$PSC_FAMILY_TMP/finite-synchronization-audit.log")" -eq 1
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true C4SolenoidCharactersAudit.lean \
    | tee "$PSC_FAMILY_TMP/solenoid-characters-audit.log"
test "$(grep -Fxc $'PSC_SOLENOID_CHARACTER_AUDIT_COMPLETE\t72\t63' "$PSC_FAMILY_TMP/solenoid-characters-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_SOLENOID_CHARACTER_REFUSAL_CONTROLS\t64' "$PSC_FAMILY_TMP/solenoid-characters-audit.log")" -eq 1
elan run "$PSC_FAMILY_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true C4CharacterOrbitsAudit.lean \
    | tee "$PSC_FAMILY_TMP/character-orbits-audit.log"
test "$(grep -Fxc $'PSC_CHARACTER_ORBIT_AUDIT_COMPLETE\t23\t21' "$PSC_FAMILY_TMP/character-orbits-audit.log")" -eq 1
test "$(grep -Fxc $'PSC_CHARACTER_ORBIT_REFUSAL_CONTROLS\t36' "$PSC_FAMILY_TMP/character-orbits-audit.log")" -eq 1
psc_family_check_pins
