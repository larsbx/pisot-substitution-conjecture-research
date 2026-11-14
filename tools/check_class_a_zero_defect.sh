#!/usr/bin/env bash
# Fresh-source gate for the explicitly scoped Class-A occurrence theorems.
# The full thirteen-case written/native theorem is not a Lean endpoint here.
set -euo pipefail
PSC_ESCAPE_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_ESCAPE_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_ESCAPE_TMP"' EXIT
python3 "$PSC_ESCAPE_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_ESCAPE_TMP/proof/PscVerif"
for PSC_ESCAPE_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_ESCAPE_ENV" ]]; then unset "$PSC_ESCAPE_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export MATHLIB_CACHE_DIR="$PSC_ESCAPE_TMP/download-cache"
export MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4-master"
cd "$PSC_ESCAPE_TMP/proof/PscVerif"
PSC_ESCAPE_PIN=$(cat lean-toolchain)
PSC_ESCAPE_RELEASE=${PSC_ESCAPE_PIN#leanprover/lean4:v}
PSC_ESCAPE_LEAN_VERSION=$(elan run "$PSC_ESCAPE_PIN" lean --version)
PSC_ESCAPE_LAKE_VERSION=$(elan run "$PSC_ESCAPE_PIN" lake --version)
if [[ "$PSC_ESCAPE_LEAN_VERSION" != "Lean (version $PSC_ESCAPE_RELEASE,"* ]] \
   || [[ "$PSC_ESCAPE_LAKE_VERSION" != *"(Lean version $PSC_ESCAPE_RELEASE)" ]]; then
    echo "Lean/Lake executable version does not match the pinned release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_ESCAPE_LEAN_VERSION" "$PSC_ESCAPE_LAKE_VERSION"
psc_escape_check_pins() {
    for PSC_ESCAPE_CONFIG in lean-toolchain lakefile.toml lake-manifest.json; do
        cmp "$PSC_ESCAPE_ROOT/proof/PscVerif/$PSC_ESCAPE_CONFIG" "$PSC_ESCAPE_CONFIG"
    done
    python3 - "$PSC_ESCAPE_ROOT" "$PSC_ESCAPE_TMP" <<'PY'
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / "tools"))
from make_proof_bank import check_pins
check_pins(pathlib.Path(sys.argv[2]), require_packages=True)
PY
}
elan run "$PSC_ESCAPE_PIN" lake --no-cache env true
psc_escape_check_pins
elan run "$PSC_ESCAPE_PIN" lake --no-cache exe cache get
elan run "$PSC_ESCAPE_PIN" lake --no-cache build PscVerif.ClassAZeroDefectEscape
psc_escape_check_pins
elan run "$PSC_ESCAPE_PIN" lake --no-cache env lean ClassAZeroDefectEscapeAudit.lean \
    | tee "$PSC_ESCAPE_TMP/audit.log"
python3 - "$PSC_ESCAPE_TMP/audit.log" <<'PY'
from pathlib import Path
import sys
prefix = "PSC_CLASS_A_ESCAPE"
rows = [line.split("\t") for line in Path(sys.argv[1]).read_text().splitlines()]
expected = {"Psc.ClassAZeroDefectEscape." + name for name in (
    "overrun_four_digit_steps", "overrun_four_steps", "overrun_composable_path",
    "run_slice_two_digit_steps", "run_slice_two_steps")}
found = [row[1] for row in rows if row[0] == prefix + "_ENDPOINT"]
if len(found) != len(expected) or set(found) != expected:
    raise SystemExit("missing, duplicate or unexpected exact-type Lean endpoint")
complete = [row for row in rows if row[0] == prefix + "_AUDIT_COMPLETE"]
if complete != [[prefix + "_AUDIT_COMPLETE", "5", "15"]]:
    raise SystemExit("missing endpoint negative-control completion receipt")
modules = [row for row in rows if row[0] == prefix + "_MODULE"]
if len(modules) != 1 or modules[0][1] != "PscVerif.ClassAZeroDefectEscape":
    raise SystemExit("new module was not exhaustively audited")
declarations = [row for row in rows if row[0] == prefix + "_DECLARATIONS"]
if len(declarations) != 1 or declarations[0][1] != "1":
    raise SystemExit("missing owned-declaration audit completion")
PY
psc_escape_check_pins
