#!/usr/bin/env bash
# Compile the beta-numeration modules and their dependency closure from isolated
# sources, then replay the endpoint axiom audit. Local .olean files and Lake
# configuration are never copied into this gate.
set -euo pipefail
PSC_BETA_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_BETA_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_BETA_TMP"' EXIT
python3 "$PSC_BETA_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_BETA_TMP/proof/PscVerif"
for PSC_BETA_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_BETA_ENV" ]]; then unset "$PSC_BETA_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export MATHLIB_CACHE_DIR="$PSC_BETA_TMP/download-cache"
export MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4-master"
cd "$PSC_BETA_TMP/proof/PscVerif"
PSC_BETA_PIN=$(cat lean-toolchain)
PSC_BETA_RELEASE=${PSC_BETA_PIN#leanprover/lean4:v}
PSC_BETA_LEAN_VERSION=$(elan run "$PSC_BETA_PIN" lean --version)
PSC_BETA_LAKE_VERSION=$(elan run "$PSC_BETA_PIN" lake --version)
if [[ "$PSC_BETA_LEAN_VERSION" != "Lean (version $PSC_BETA_RELEASE,"* ]] \
   || [[ "$PSC_BETA_LAKE_VERSION" != *"(Lean version $PSC_BETA_RELEASE)" ]]; then
    echo "Lean/Lake executable version does not match the pinned release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_BETA_LEAN_VERSION" "$PSC_BETA_LAKE_VERSION"
psc_beta_check_pins() {
    for PSC_BETA_CONFIG in lean-toolchain lakefile.toml lake-manifest.json; do
        cmp "$PSC_BETA_ROOT/proof/PscVerif/$PSC_BETA_CONFIG" "$PSC_BETA_CONFIG"
    done
    python3 - "$PSC_BETA_ROOT" "$PSC_BETA_TMP" <<'PY'
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / "tools"))
from make_proof_bank import check_pins
check_pins(pathlib.Path(sys.argv[2]), require_packages=True)
PY
}
elan run "$PSC_BETA_PIN" lake --no-cache env true
psc_beta_check_pins
elan run "$PSC_BETA_PIN" lake --no-cache exe cache get
elan run "$PSC_BETA_PIN" lake --no-cache build \
    PscVerif.WordComplexity PscVerif.BetaNumeration PscVerif.BetaMetallic \
    PscVerif.C4FamilyFixedWord PscVerif.C4FamilyBetaTranscendence \
    PscVerif.BetaGoldenEndpoint
psc_beta_check_pins
elan run "$PSC_BETA_PIN" lake --no-cache env lean \
    -DautoImplicit=false -Dpp.unicode.fun=true BetaNumerationAudit.lean \
    | tee "$PSC_BETA_TMP/beta-audit.log"
test "$(grep -c '^PSC_BETA_ENDPOINT' "$PSC_BETA_TMP/beta-audit.log")" -eq 24
test "$(grep -Fxc $'PSC_BETA_AUDIT_COMPLETE\t24' "$PSC_BETA_TMP/beta-audit.log")" -eq 1
