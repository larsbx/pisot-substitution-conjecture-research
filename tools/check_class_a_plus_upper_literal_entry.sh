#!/usr/bin/env bash
# Source-bound local acceptance: rebuild every project dependency in an empty
# project artifact tree. Reuse only the manifest-pinned upstream package cache.
# An absent dependency/cache or a changed source refuses this acceptance run.
set -euo pipefail
PSC_ENTRY_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_ENTRY_TEMP=$(mktemp -d)
trap 'rm -rf "$PSC_ENTRY_TEMP"' EXIT
PSC_ENTRY_PACKAGES=${PSC_ENTRY_PACKAGES:-"$PSC_ENTRY_ROOT/proof/PscVerif/.lake/packages"}
PSC_ENTRY_EVIDENCE_DIR=${PSC_ENTRY_EVIDENCE_DIR:-$(mktemp -d)}
mkdir -p "$PSC_ENTRY_EVIDENCE_DIR"
PSC_ENTRY_EVIDENCE_DIR=$(cd "$PSC_ENTRY_EVIDENCE_DIR" && pwd -P)
python3 - "$PSC_ENTRY_ROOT" "$PSC_ENTRY_TEMP" "$PSC_ENTRY_PACKAGES" "$PSC_ENTRY_EVIDENCE_DIR" <<'PY'
import hashlib, json, pathlib, re, sys
root, temporary, packages, evidence = map(pathlib.Path, sys.argv[1:])
sys.path.insert(0, str(root / "tools"))
from make_proof_bank import prepare_audit_workspace, check_pins, lean_code
project = root / "proof/PscVerif"
fresh = temporary / "proof/PscVerif"
prepare_audit_workspace(root, fresh)
packages = packages.resolve(strict=True)
(fresh / ".lake").mkdir()
(fresh / ".lake/packages").symlink_to(packages, target_is_directory=True)
pins = check_pins(temporary, require_packages=True)
(evidence / "pins.json").write_text(json.dumps(pins, indent=2)+"\n")
paths = [project / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
paths += sorted(project.glob("*.lean")) + sorted((project / "PscVerif").rglob("*.lean"))
manifest = {p.relative_to(project).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
for name, digest in manifest.items():
    if hashlib.sha256((fresh / name).read_bytes()).hexdigest() != digest:
        raise SystemExit("copied source mismatch: " + name)
encoded = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode()
(evidence / "source-bindings.json").write_bytes(encoded)
helpers = {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in
    ("tools/make_proof_bank.py", "tools/check_class_a_plus_upper_literal_entry.sh")}
(evidence / "gate-bindings.json").write_text(json.dumps(helpers, sort_keys=True)+"\n")
visited = set()
def visit(module):
    if module in visited:
        return
    path = fresh / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise SystemExit("missing local source: " + module)
    visited.add(module)
    for match in re.finditer(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)$", lean_code(path.read_text())):
        for dependency in match[1].split():
            if dependency.startswith("PscVerif."):
                visit(dependency)
for module in ("PscVerif.ClassAPlusUpperEntryBound", "PscVerif.ClassAPlusUpperEntryControls",
               "ClassAPlusUpperLiteralEntryAudit", "ClassAPlusUpperEntryControlsAudit",
               "ClassAPlusUpperEntryAudit"):
    visit(module)
(evidence / "local-imports.json").write_text(json.dumps(sorted(visited), indent=2)+"\n")
print("PSC_UPPER_LITERAL_SOURCE_SNAPSHOT", len(manifest), hashlib.sha256(encoded).hexdigest(), sep="\t")
print("PSC_UPPER_LITERAL_LOCAL_IMPORTS", len(visited), sep="\t")
print("PSC_UPPER_LITERAL_CACHE_POLICY\tpinned-upstream-cache\tno-project-artifacts")
PY
for PSC_ENTRY_ENV in "${!LEAN_@}" "${!LAKE_@}"; do
    if [[ -n "$PSC_ENTRY_ENV" ]]; then unset "$PSC_ENTRY_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
cd "$PSC_ENTRY_TEMP/proof/PscVerif"
PSC_ENTRY_PIN=$(cat lean-toolchain)
PSC_ENTRY_RELEASE=${PSC_ENTRY_PIN#leanprover/lean4:v}
PSC_ENTRY_LEAN_VERSION=$(lean --version)
PSC_ENTRY_LAKE_VERSION=$(lake --version)
if [[ "$PSC_ENTRY_LEAN_VERSION" != "Lean (version $PSC_ENTRY_RELEASE,"* ]] \
    || [[ "$PSC_ENTRY_LAKE_VERSION" != *"(Lean version $PSC_ENTRY_RELEASE)" ]]; then
    echo "Lean/Lake executable does not match the exact project release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_ENTRY_LEAN_VERSION" "$PSC_ENTRY_LAKE_VERSION" | tee "$PSC_ENTRY_EVIDENCE_DIR/versions.txt"
if [[ -d .lake/build ]]; then
    echo "Unexpected project build artifact before isolated compilation" >&2
    exit 1
fi
lake --no-cache build PscVerif.ClassAPlusUpperEntryBound PscVerif.ClassAPlusUpperEntryControls \
    2>&1 | tee "$PSC_ENTRY_EVIDENCE_DIR/build.log"
lake --no-cache env lean ClassAPlusUpperLiteralEntryAudit.lean \
    2>&1 | tee "$PSC_ENTRY_EVIDENCE_DIR/audit.log"
lake --no-cache env lean ClassAPlusUpperEntryControlsAudit.lean \
    2>&1 | tee "$PSC_ENTRY_EVIDENCE_DIR/controls-audit.log"
lake --no-cache env lean ClassAPlusUpperEntryAudit.lean \
    2>&1 | tee "$PSC_ENTRY_EVIDENCE_DIR/arithmetic-audit.log"
python3 - "$PSC_ENTRY_ROOT" "$PSC_ENTRY_TEMP" "$PSC_ENTRY_EVIDENCE_DIR" <<'PY'
import hashlib, json, pathlib, sys
root, temporary, evidence = map(pathlib.Path, sys.argv[1:])
manifest = json.loads((evidence / "source-bindings.json").read_bytes())
for project in (root / "proof/PscVerif", temporary / "proof/PscVerif"):
    paths = [project / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    paths += sorted(project.glob("*.lean")) + sorted((project / "PscVerif").rglob("*.lean"))
    actual = {p.relative_to(project).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    if actual != manifest:
        raise SystemExit("project source changed during isolated acceptance: " + str(project))
for name, expected in json.loads((evidence / "gate-bindings.json").read_text()).items():
    if hashlib.sha256((root / name).read_bytes()).hexdigest() != expected:
        raise SystemExit("gate source changed during acceptance: " + name)
sys.path.insert(0, str(root / "tools"))
from make_proof_bank import check_pins
check_pins(temporary, require_packages=True)
audit = (evidence / "audit.log").read_text()
if "PSC_UPPER_LITERAL_AUDIT_COMPLETE" not in audit:
    raise SystemExit("missing compiled endpoint/axiom audit completion receipt")
print("PSC_UPPER_LITERAL_SOURCE_RECHECK", len(manifest),
    hashlib.sha256((evidence / "source-bindings.json").read_bytes()).hexdigest(), sep="\t")
print("PSC_UPPER_LITERAL_GATE_COMPLETE\t3-audit-fixtures\tfresh-project-compilation")
PY
printf 'PSC_UPPER_LITERAL_EVIDENCE\t%s\n' "$PSC_ENTRY_EVIDENCE_DIR"
