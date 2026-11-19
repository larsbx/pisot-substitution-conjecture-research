#!/usr/bin/env bash
# Fresh local sources and pinned dependency checkouts; only selected upstream
# source-hash artifacts may be restored. Compile and audit the complete local
# periodic-partner import closure, without reusing local objects.
set -euo pipefail
PSC_PERIODIC_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_PERIODIC_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_PERIODIC_TMP"' EXIT
python3 "$PSC_PERIODIC_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_PERIODIC_TMP/proof/PscVerif"
python3 - "$PSC_PERIODIC_ROOT" "$PSC_PERIODIC_TMP" <<'PY'
import hashlib, json, pathlib, re, shutil, sys
root = pathlib.Path(sys.argv[1])
project = root / "proof/PscVerif"
temporary = pathlib.Path(sys.argv[2])
fresh = temporary / "proof/PscVerif"
paths = [project / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
paths += sorted(project.glob("*.lean")) + sorted((project / "PscVerif").rglob("*.lean"))
manifest = {}
for source in paths:
    relative = source.relative_to(project).as_posix()
    contents = source.read_bytes()
    if (fresh / relative).read_bytes() != contents:
        raise SystemExit("isolated source differs: " + relative)
    manifest[relative] = hashlib.sha256(contents).hexdigest()
encoded = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
(temporary / "source-bindings.json").write_bytes(encoded)
print("PSC_PERIODIC_PARTNER_SOURCE_SNAPSHOT", len(manifest), hashlib.sha256(encoded).hexdigest(), sep="\t")
for relative, digest in sorted(manifest.items()):
    print("PSC_PERIODIC_PARTNER_SOURCE", relative, digest, sep="\t")
support = {n: hashlib.sha256((root / n).read_bytes()).hexdigest() for n in
           ("tools/check_c4_periodic_partner.sh", "tools/make_proof_bank.py")}
(temporary / "support-bindings.json").write_text(json.dumps(support, sort_keys=True))
sys.path.insert(0, str(root / "tools"))
from make_proof_bank import lean_code, lean_declarations
visited, external = set(), set()
def visit(module):
    if module in visited:
        return
    path = fresh / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise SystemExit("missing fresh local import: " + module)
    visited.add(module)
    code = lean_code(path.read_text())
    for match in re.finditer(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)$", code):
        for dependency in match[1].split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", dependency):
                raise SystemExit("unsupported import syntax: " + dependency)
            if dependency == "PscVerif" or dependency.startswith("PscVerif."):
                visit(dependency)
            elif dependency.split(".")[0] not in {"Lean", "Init", "Lake"}:
                external.add(dependency)
visit("PscVerif.PeriodicPartner")
visit("PscVerif.PeriodicPartnerControls")
visit("PeriodicPartnerAudit")
if not external or "Mathlib" in external:
    raise SystemExit("refuse empty or whole-Mathlib cache request")
(temporary / "external-roots.txt").write_text("\n".join(sorted(external)) + "\n")
owned = sorted(m for m in visited if m == "PscVerif" or m.startswith("PscVerif."))
(temporary / "local-modules.json").write_text(json.dumps(owned))
expected = sorted((d["module"], d["name"]) for d in lean_declarations(temporary)
                  if d["module"] in owned)
if not expected:
    raise SystemExit("empty named theorem inventory for scoped audit")
(temporary / "expected-proofs.json").write_text(json.dumps(expected))
print("PSC_PERIODIC_PARTNER_EXPECTED_PROOFS", len(expected), sep="\t")
for module in sorted(visited):
    print("PSC_PERIODIC_PARTNER_LOCAL_IMPORT", module, sep="\t")
for module in sorted(external):
    print("PSC_PERIODIC_PARTNER_UPSTREAM_ROOT", module, sep="\t")
if shutil.disk_usage(temporary).free < 4 * 1024**3:
    raise SystemExit("refuse fresh scoped build with less than 4 GiB free")
PY
# No inherited local build/cache directory may influence this fresh project.
for PSC_PERIODIC_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_PERIODIC_ENV" ]]; then unset "$PSC_PERIODIC_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export MATHLIB_CACHE_DIR="$PSC_PERIODIC_TMP/download-cache"
export MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4-master"
cd "$PSC_PERIODIC_TMP/proof/PscVerif"
PSC_PERIODIC_PIN=$(cat lean-toolchain)
PSC_PERIODIC_RELEASE=${PSC_PERIODIC_PIN#leanprover/lean4:v}
if command -v elan >/dev/null 2>&1; then
    PSC_PERIODIC_LEAN=(elan run "$PSC_PERIODIC_PIN" lean)
    PSC_PERIODIC_LAKE=(elan run "$PSC_PERIODIC_PIN" lake)
else
    PSC_PERIODIC_LEAN=("$(command -v lean)")
    PSC_PERIODIC_LAKE=("$(command -v lake)")
fi
PSC_PERIODIC_LEAN_VERSION=$("${PSC_PERIODIC_LEAN[@]}" --version)
PSC_PERIODIC_LAKE_VERSION=$("${PSC_PERIODIC_LAKE[@]}" --version)
if [[ "$PSC_PERIODIC_LEAN_VERSION" != "Lean (version $PSC_PERIODIC_RELEASE,"* ]] \
   || [[ "$PSC_PERIODIC_LAKE_VERSION" != *"(Lean version $PSC_PERIODIC_RELEASE)" ]]; then
    echo "Lean/Lake executable version does not match the pinned release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_PERIODIC_LEAN_VERSION" "$PSC_PERIODIC_LAKE_VERSION"
printf 'PSC_PERIODIC_PARTNER_CACHE_POLICY\tfresh-pinned-dependencies\tselected-upstream-source-hash-cache\tno-local-artifacts\n'
psc_periodic_check_sources_and_pins() {
    python3 - "$PSC_PERIODIC_ROOT" "$PSC_PERIODIC_TMP" "$1" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
temporary = pathlib.Path(sys.argv[2])
manifest = json.loads((temporary / "source-bindings.json").read_bytes())
for project in (root / "proof/PscVerif", temporary / "proof/PscVerif"):
    paths = [project / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    paths += sorted(project.glob("*.lean")) + sorted((project / "PscVerif").rglob("*.lean"))
    actual = {p.relative_to(project).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    if actual != manifest:
        raise SystemExit("source or pin changed during isolated acceptance: " + str(project))
for relative, expected in json.loads((temporary / "support-bindings.json").read_text()).items():
    if hashlib.sha256((root / relative).read_bytes()).hexdigest() != expected:
        raise SystemExit("acceptance support changed during replay: " + relative)
sys.path.insert(0, str(root / "tools"))
from make_proof_bank import check_pins
check_pins(temporary, require_packages=True)
encoded = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
print("PSC_PERIODIC_PARTNER_SOURCE_RECHECK", sys.argv[3], len(manifest),
      hashlib.sha256(encoded).hexdigest(), sep="\t")
PY
}
"${PSC_PERIODIC_LAKE[@]}" --no-cache env true
psc_periodic_check_sources_and_pins after-clone
mapfile -t PSC_PERIODIC_EXTERNAL_ROOTS < "$PSC_PERIODIC_TMP/external-roots.txt"
# The pinned Cache.IO.spawnLeanTarDecompress supplies no --jobs argument.
# Bound leantar's Rayon pool: its default scales with all available CPUs and
# can exhaust memory while cache downloads and decompression overlap.
printf 'PSC_PERIODIC_PARTNER_CACHE_THREADS\tRAYON_NUM_THREADS\t2\n'
RAYON_NUM_THREADS=2 "${PSC_PERIODIC_LAKE[@]}" --no-cache exe cache get "${PSC_PERIODIC_EXTERNAL_ROOTS[@]}"
psc_periodic_check_sources_and_pins after-upstream-cache
if [[ -d .lake/build/lib/lean/PscVerif || -e .lake/build/lib/lean/PscVerif.olean ]]; then
    echo "unexpected local project artifacts before fresh compilation" >&2
    exit 1
fi
"${PSC_PERIODIC_LAKE[@]}" --no-cache build PscVerif.PeriodicPartner PscVerif.PeriodicPartnerControls \
    PscVerif.PeriodicPartnerDynamics PscVerif.PeriodicPartnerCollapse PscVerif.PeriodicPartnerModels \
    PscVerif.PeriodicPartnerDichotomy PscVerif.PeriodicPartnerReflection \
    PscVerif.PeriodicPartnerAsymptotic PscVerif.PeriodicPartnerHull \
    PscVerif.PeriodicPartnerSelection
psc_periodic_check_sources_and_pins after-build
"${PSC_PERIODIC_LAKE[@]}" --no-cache env lean PeriodicPartnerAudit.lean \
    | tee "$PSC_PERIODIC_TMP/audit.log"
python3 - "$PSC_PERIODIC_ROOT" "$PSC_PERIODIC_TMP" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
temporary = pathlib.Path(sys.argv[2])
sys.path.insert(0, str(root / "tools"))
from make_proof_bank import check_audit
expected = {tuple(row) for row in json.loads((temporary / "expected-proofs.json").read_text())}
modules = set(json.loads((temporary / "local-modules.json").read_text()))
log = (temporary / "audit.log").read_text()
declarations, theorems = check_audit(log, expected)
reached = {line.split("\t")[2] for line in log.splitlines() if line.startswith("PSC_AXIOMS\t")}
if reached != modules:
    raise SystemExit("compiled module coverage differs from source import closure")
print("PSC_PERIODIC_PARTNER_AUDIT_VERIFIED", len(modules), declarations, theorems,
      len(expected), sep="\t")
PY
psc_periodic_check_sources_and_pins after-audit
printf 'PSC_PERIODIC_PARTNER_GATE_COMPLETE\tfresh-local-closure\tstandard-axioms-only\n'
