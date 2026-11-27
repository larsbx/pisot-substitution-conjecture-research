#!/usr/bin/env bash
# Fresh project-object replay of the diagonal components and finite certificates.
set -euo pipefail
PSC_DIAGONAL_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_DIAGONAL_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_DIAGONAL_TMP"' EXIT
PSC_DIAGONAL_OUT=${PSC_DIAGONAL_EVIDENCE_DIR:-"$PSC_DIAGONAL_TMP/receipts"}
PSC_DIAGONAL_MOJO=${PSC_MOJO:-mojo}
mkdir -p "$PSC_DIAGONAL_OUT"
if [[ -n "$(ls -A "$PSC_DIAGONAL_OUT")" ]]; then
    echo "Evidence directory must be empty; existing receipts are preserved" >&2
    exit 1
fi
PSC_DIAGONAL_OUT=$(cd "$PSC_DIAGONAL_OUT" && pwd -P)

psc_diagonal_bindings() {
    python3 - "$PSC_DIAGONAL_ROOT" <<'PY'
import hashlib, json, pathlib, subprocess, sys
root = pathlib.Path(sys.argv[1])
paths = sorted(set(subprocess.check_output([
    'git', '-C', str(root), 'ls-files', '--cached', '--others', '--exclude-standard',
    '--', 'proof/PscVerif', 'kernel', 'tools/check_bh_diagonal_residual.sh',
    'tools/make_proof_bank.py', 'oracles/python/bh_diagonal_residual.py',
    'tests/test_bh_diagonal_residual_oracle.py', 'vendored.toml',
]).decode().splitlines()))
print(json.dumps({p: hashlib.sha256((root/p).read_bytes()).hexdigest()
                  for p in paths if (root/p).is_file()}, indent=2, sort_keys=True))
PY
}
psc_diagonal_bindings > "$PSC_DIAGONAL_OUT/source-bindings.json"
python3 "$PSC_DIAGONAL_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_DIAGONAL_TMP/proof/PscVerif"
python3 "$PSC_DIAGONAL_ROOT/tools/make_proof_bank.py" --pins-only --require-packages
mkdir -p "$PSC_DIAGONAL_TMP/proof/PscVerif/.lake"
ln -s "$PSC_DIAGONAL_ROOT/proof/PscVerif/.lake/packages" \
    "$PSC_DIAGONAL_TMP/proof/PscVerif/.lake/packages"
for PSC_DIAGONAL_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_DIAGONAL_ENV" ]]; then unset "$PSC_DIAGONAL_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
cd "$PSC_DIAGONAL_TMP/proof/PscVerif"
PSC_DIAGONAL_PIN=$(cat lean-toolchain)
PSC_DIAGONAL_RELEASE=${PSC_DIAGONAL_PIN#leanprover/lean4:v}
PSC_DIAGONAL_VERSION=$(lean --version)
if [[ "$PSC_DIAGONAL_VERSION" != "Lean (version $PSC_DIAGONAL_RELEASE,"* ]]; then
    echo "Lean executable does not match the repository pin" >&2
    exit 1
fi
printf '%s\n' "$PSC_DIAGONAL_VERSION" > "$PSC_DIAGONAL_OUT/versions.log"
lake --version >> "$PSC_DIAGONAL_OUT/versions.log"
"$PSC_DIAGONAL_MOJO" --version >> "$PSC_DIAGONAL_OUT/versions.log"
python3 --version >> "$PSC_DIAGONAL_OUT/versions.log"
lake --no-cache build PscVerif.BHDiagonalCertificate PscVerif.BHDiagonalDescent \
    PscVerif.BHDiagonalAxis PscVerif.BHDiagonalClassification \
    > "$PSC_DIAGONAL_OUT/lean-build.log" 2>&1
lake --no-cache env lean BHDiagonalResidualAudit.lean \
    > "$PSC_DIAGONAL_OUT/lean-audit.log" 2>&1
lake --no-cache env lean BHDiagonalLiteralAudit.lean \
    > "$PSC_DIAGONAL_OUT/literal-audit.log" 2>&1
lake --no-cache env lean BHNearDiagonalAudit.lean \
    > "$PSC_DIAGONAL_OUT/near-diagonal-audit.log" 2>&1
python3 - "$PSC_DIAGONAL_OUT/lean-audit.log" <<'PY'
import pathlib, sys
rows = pathlib.Path(sys.argv[1]).read_text().splitlines()
assert sum(row.startswith('PSC_BH_DIAGONAL_ENDPOINT\t') for row in rows) == 18
assert sum(row.startswith('PSC_BH_DIAGONAL_MODULE\t') for row in rows) == 6
assert rows.count('PSC_BH_DIAGONAL_AUDIT_COMPLETE\t18\t6') == 1
PY
cd "$PSC_DIAGONAL_ROOT/kernel"
"$PSC_DIAGONAL_MOJO" run -I . -I tests tests/test_bh_diagonal_residual.mojo \
    > "$PSC_DIAGONAL_OUT/native-test.log" 2>&1
"$PSC_DIAGONAL_MOJO" run -I . bh_diagonal_residual.mojo \
    > "$PSC_DIAGONAL_OUT/residual-certificates.csv" 2> "$PSC_DIAGONAL_OUT/native-export.log"
cd "$PSC_DIAGONAL_ROOT"
python3 oracles/python/bh_diagonal_residual.py \
    --native-csv "$PSC_DIAGONAL_OUT/residual-certificates.csv" \
    > "$PSC_DIAGONAL_OUT/independent-oracle.json"
python3 -m pytest -q tests/test_bh_diagonal_residual_oracle.py \
    > "$PSC_DIAGONAL_OUT/oracle-controls.log" 2>&1
python3 tools/make_proof_bank.py --pins-only --require-packages
psc_diagonal_bindings > "$PSC_DIAGONAL_TMP/source-bindings-after.json"
cmp "$PSC_DIAGONAL_OUT/source-bindings.json" "$PSC_DIAGONAL_TMP/source-bindings-after.json"
printf '%s\n' 'Scoped diagonal components and exact finite replay passed; complete family assembly is checked by check_bh_diagonal_closure.sh.'
