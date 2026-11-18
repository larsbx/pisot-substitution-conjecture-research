#!/usr/bin/env bash
# Fresh project sources, fresh pinned dependency checkouts, selected upstream
# source-hash artifacts, then fresh compilation of every local dependency.
# A direct pinned Lean/Lake installation is accepted when Elan is unavailable;
# both executable versions are checked against the exact checked-in release.
set -euo pipefail
PSC_UPPER_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_UPPER_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_UPPER_TMP"' EXIT
python3 "$PSC_UPPER_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_UPPER_TMP/proof/PscVerif"
python3 - "$PSC_UPPER_ROOT" "$PSC_UPPER_TMP" <<'PY'
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
print("PSC_CLASS_A_PLUS_UPPER_SOURCE_SNAPSHOT", len(manifest), hashlib.sha256(encoded).hexdigest(), sep="\t")
for relative, digest in sorted(manifest.items()):
    print("PSC_CLASS_A_PLUS_UPPER_SOURCE", relative, digest, sep="\t")
sys.path.insert(0, str(root / "tools"))
from make_proof_bank import lean_code
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
            if dependency.startswith("PscVerif."):
                visit(dependency)
            elif dependency.split(".")[0] not in {"Lean", "Init", "Lake"}:
                external.add(dependency)
visit("PscVerif.ClassAPlusUpperCycles")
visit("ClassAPlusUpperCyclesAudit")
if not external or "Mathlib" in external:
    raise SystemExit("refuse empty or whole-Mathlib cache request")
(temporary / "external-roots.txt").write_text("\n".join(sorted(external)) + "\n")
print("PSC_CLASS_A_PLUS_UPPER_LOCAL_IMPORT_CLOSURE", len(visited), sep="\t")
for module in sorted(visited):
    print("PSC_CLASS_A_PLUS_UPPER_LOCAL_IMPORT", module, sep="\t")
for module in sorted(external):
    print("PSC_CLASS_A_PLUS_UPPER_UPSTREAM_ROOT", module, sep="\t")
if shutil.disk_usage(temporary).free < 12 * 1024**3:
    raise SystemExit("refuse fresh build with less than 12 GiB free")
PY
# Clear inherited artifact locations and alternative upstream-cache settings.
for PSC_UPPER_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_UPPER_ENV" ]]; then unset "$PSC_UPPER_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export MATHLIB_CACHE_DIR="$PSC_UPPER_TMP/download-cache"
export MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4-master"
cd "$PSC_UPPER_TMP/proof/PscVerif"
PSC_UPPER_PIN=$(cat lean-toolchain)
PSC_UPPER_RELEASE=${PSC_UPPER_PIN#leanprover/lean4:v}
if command -v elan >/dev/null 2>&1; then
    PSC_UPPER_LEAN=(elan run "$PSC_UPPER_PIN" lean)
    PSC_UPPER_LAKE=(elan run "$PSC_UPPER_PIN" lake)
else
    PSC_UPPER_LEAN=("$(command -v lean)")
    PSC_UPPER_LAKE=("$(command -v lake)")
fi
PSC_UPPER_LEAN_VERSION=$("${PSC_UPPER_LEAN[@]}" --version)
PSC_UPPER_LAKE_VERSION=$("${PSC_UPPER_LAKE[@]}" --version)
if [[ "$PSC_UPPER_LEAN_VERSION" != "Lean (version $PSC_UPPER_RELEASE,"* ]] \
   || [[ "$PSC_UPPER_LAKE_VERSION" != *"(Lean version $PSC_UPPER_RELEASE)" ]]; then
    echo "Lean/Lake executable version does not match the pinned release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_UPPER_LEAN_VERSION" "$PSC_UPPER_LAKE_VERSION"
printf 'PSC_CLASS_A_PLUS_UPPER_CACHE_POLICY\tfresh-pinned-dependencies\tselected-upstream-source-hash-cache\tno-local-artifacts\n'
psc_upper_check_sources_and_pins() {
    python3 - "$PSC_UPPER_ROOT" "$PSC_UPPER_TMP" "$1" <<'PY'
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
encoded = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
print("PSC_CLASS_A_PLUS_UPPER_SOURCE_RECHECK", sys.argv[3], len(manifest),
      hashlib.sha256(encoded).hexdigest(), sep="\t")
PY
}
"${PSC_UPPER_LAKE[@]}" --no-cache env true
psc_upper_check_sources_and_pins after-clone
mapfile -t PSC_UPPER_EXTERNAL_ROOTS < "$PSC_UPPER_TMP/external-roots.txt"
"${PSC_UPPER_LAKE[@]}" --no-cache exe cache get "${PSC_UPPER_EXTERNAL_ROOTS[@]}"
psc_upper_check_sources_and_pins after-upstream-cache
# No project .olean was copied or requested from the upstream cache.
if [[ -d .lake/build/lib/lean/PscVerif ]]; then
    echo "unexpected local project artifacts before fresh compilation" >&2
    exit 1
fi
"${PSC_UPPER_LAKE[@]}" --no-cache build PscVerif.ClassAPlusUpperCycles
psc_upper_check_sources_and_pins after-build
"${PSC_UPPER_LAKE[@]}" --no-cache env lean ClassAPlusUpperCyclesAudit.lean \
    | tee "$PSC_UPPER_TMP/audit.log"
python3 "$PSC_UPPER_ROOT/tools/check_class_a_plus_upper_audit.py" "$PSC_UPPER_TMP/audit.log"
psc_upper_check_sources_and_pins after-audit
printf 'PSC_CLASS_A_PLUS_UPPER_GATE_COMPLETE\t2\t167\t114\t8\t24\n'
