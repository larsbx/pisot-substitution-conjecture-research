#!/usr/bin/env bash
# Fresh-source acceptance for the seven scoped central-recurrence endpoints.
# The finite-block entry proof and the complete zero-hit theorem have separate
# written/native scopes; this gate does not silently formalize them.
set -euo pipefail
PSC_CENTRAL_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_CENTRAL_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_CENTRAL_TMP"' EXIT
python3 "$PSC_CENTRAL_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_CENTRAL_TMP/proof/PscVerif"
python3 - "$PSC_CENTRAL_ROOT" "$PSC_CENTRAL_TMP" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1]) / "proof/PscVerif"
fresh = pathlib.Path(sys.argv[2]) / "proof/PscVerif"
paths = [root / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
paths += sorted(root.glob("*.lean")) + sorted((root / "PscVerif").rglob("*.lean"))
manifest = {}
for source in paths:
    relative = source.relative_to(root).as_posix()
    contents = source.read_bytes()
    if (fresh / relative).read_bytes() != contents:
        raise SystemExit("isolated source differs before compilation: " + relative)
    manifest[relative] = hashlib.sha256(contents).hexdigest()
encoded = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
(pathlib.Path(sys.argv[2]) / "source-bindings.json").write_bytes(encoded)
print("PSC_CLASS_A_CENTRAL_SOURCE_SNAPSHOT", len(manifest), hashlib.sha256(encoded).hexdigest(), sep="\t")
for relative, digest in sorted(manifest.items()):
    print("PSC_CLASS_A_CENTRAL_SOURCE", relative, digest, sep="\t")
PY
# Never inherit a caller's local Lean/Lake artifact cache or configuration.
for PSC_CENTRAL_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_CENTRAL_ENV" ]]; then unset "$PSC_CENTRAL_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export MATHLIB_CACHE_DIR="$PSC_CENTRAL_TMP/download-cache"
export MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4-master"
cd "$PSC_CENTRAL_TMP/proof/PscVerif"
PSC_CENTRAL_PIN=$(cat lean-toolchain)
PSC_CENTRAL_RELEASE=${PSC_CENTRAL_PIN#leanprover/lean4:v}
PSC_CENTRAL_LEAN_VERSION=$(elan run "$PSC_CENTRAL_PIN" lean --version)
PSC_CENTRAL_LAKE_VERSION=$(elan run "$PSC_CENTRAL_PIN" lake --version)
if [[ "$PSC_CENTRAL_LEAN_VERSION" != "Lean (version $PSC_CENTRAL_RELEASE,"* ]] \
   || [[ "$PSC_CENTRAL_LAKE_VERSION" != *"(Lean version $PSC_CENTRAL_RELEASE)" ]]; then
    echo "Lean/Lake executable version does not match the pinned release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_CENTRAL_LEAN_VERSION" "$PSC_CENTRAL_LAKE_VERSION"
printf 'PSC_CLASS_A_CENTRAL_CACHE_POLICY\tfresh-pinned-dependencies\tupstream-source-hash-cache\tno-local-artifacts\n'
psc_central_check_sources_and_pins() {
    python3 - "$PSC_CENTRAL_ROOT" "$PSC_CENTRAL_TMP" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1]) / "proof/PscVerif"
fresh = pathlib.Path(sys.argv[2]) / "proof/PscVerif"
manifest = json.loads((pathlib.Path(sys.argv[2]) / "source-bindings.json").read_bytes())
for project in (root, fresh):
    paths = [project / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    paths += sorted(project.glob("*.lean")) + sorted((project / "PscVerif").rglob("*.lean"))
    actual = {p.relative_to(project).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    if actual != manifest:
        raise SystemExit("source or pin changed during isolated acceptance: " + str(project))
sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / "tools"))
from make_proof_bank import check_pins
check_pins(pathlib.Path(sys.argv[2]), require_packages=True)
PY
}
elan run "$PSC_CENTRAL_PIN" lake --no-cache env true
psc_central_check_sources_and_pins
elan run "$PSC_CENTRAL_PIN" lake --no-cache exe cache get
elan run "$PSC_CENTRAL_PIN" lake --no-cache build PscVerif.ClassACentralRecurrence
psc_central_check_sources_and_pins
elan run "$PSC_CENTRAL_PIN" lake --no-cache env lean ClassACentralRecurrenceAudit.lean \
    | tee "$PSC_CENTRAL_TMP/audit.log"
python3 - "$PSC_CENTRAL_TMP/audit.log" <<'PY'
from pathlib import Path
import sys
prefix = "PSC_CLASS_A_CENTRAL"
rows = [line.split("\t") for line in Path(sys.argv[1]).read_text().splitlines()]
expected = {"Psc.ClassACentralRecurrence." + name for name in (
    "forward_integer_bound", "periodic_cycle_classification", "bounded_two_sided_classification",
    "central_gap_in_run", "run_gap_digit_step", "central_coordinate_recurrence",
    "eventual_alternating_tail")}
found = [row[1] for row in rows if row[0] == prefix + "_ENDPOINT"]
if len(found) != len(expected) or set(found) != expected:
    raise SystemExit("missing, duplicate or unexpected exact-type Lean endpoint")
complete = [row for row in rows if row[0] == prefix + "_AUDIT_COMPLETE"]
if complete != [[prefix + "_AUDIT_COMPLETE", "7", "21"]]:
    raise SystemExit("missing endpoint negative-control completion receipt")
modules = [row for row in rows if row[0] == prefix + "_MODULE"]
if len(modules) != 1 or len(modules[0]) != 4 or modules[0][1] != "PscVerif.ClassACentralRecurrence":
    raise SystemExit("new module was not exhaustively audited")
declarations, proofs = map(int, modules[0][2:])
if not 0 < proofs <= declarations:
    raise SystemExit("invalid owned-declaration audit counts")
decl_rows = [row for row in rows if row[0] == prefix + "_DECLARATIONS"]
if decl_rows != [[prefix + "_DECLARATIONS", "1", str(declarations), str(proofs)]]:
    raise SystemExit("missing or inconsistent owned-declaration audit completion")
PY
psc_central_check_sources_and_pins
printf 'PSC_CLASS_A_CENTRAL_GATE_COMPLETE\t7\t21\n'
