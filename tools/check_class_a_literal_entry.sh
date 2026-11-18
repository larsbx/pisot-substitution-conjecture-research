#!/usr/bin/env bash
# Fresh-source acceptance for six literal-entry modules and 33 exact endpoints.
# The all-source interval decomposition remains an explicit mathematical interface.
# Cached local PscVerif objects and alternative cache URLs are never accepted.
set -euo pipefail
PSC_LITERAL_ENTRY_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_LITERAL_ENTRY_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_LITERAL_ENTRY_TMP"' EXIT
python3 "$PSC_LITERAL_ENTRY_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_LITERAL_ENTRY_TMP/proof/PscVerif"
python3 - "$PSC_LITERAL_ENTRY_ROOT" "$PSC_LITERAL_ENTRY_TMP" <<'PY'
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
print("PSC_CLASS_A_LITERAL_ENTRY_SOURCE_SNAPSHOT", len(manifest), hashlib.sha256(encoded).hexdigest(), sep="\t")
for relative, digest in sorted(manifest.items()):
    print("PSC_CLASS_A_LITERAL_ENTRY_SOURCE", relative, digest, sep="\t")
PY
# Never inherit a caller's local Lean/Lake artifact cache or configuration.
for PSC_LITERAL_ENTRY_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_LITERAL_ENTRY_ENV" ]]; then unset "$PSC_LITERAL_ENTRY_ENV"; fi
done
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export MATHLIB_CACHE_DIR="$PSC_LITERAL_ENTRY_TMP/download-cache"
export MATHLIB_CACHE_GET_URL="https://cache.mathlib.org/mathlib4-master"
cd "$PSC_LITERAL_ENTRY_TMP/proof/PscVerif"
PSC_LITERAL_ENTRY_PIN=$(cat lean-toolchain)
PSC_LITERAL_ENTRY_RELEASE=${PSC_LITERAL_ENTRY_PIN#leanprover/lean4:v}
PSC_LITERAL_ENTRY_LEAN_VERSION=$(elan run "$PSC_LITERAL_ENTRY_PIN" lean --version)
PSC_LITERAL_ENTRY_LAKE_VERSION=$(elan run "$PSC_LITERAL_ENTRY_PIN" lake --version)
if [[ "$PSC_LITERAL_ENTRY_LEAN_VERSION" != "Lean (version $PSC_LITERAL_ENTRY_RELEASE,"* ]] \
   || [[ "$PSC_LITERAL_ENTRY_LAKE_VERSION" != *"(Lean version $PSC_LITERAL_ENTRY_RELEASE)" ]]; then
    echo "Lean/Lake executable version does not match the pinned release" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_LITERAL_ENTRY_LEAN_VERSION" "$PSC_LITERAL_ENTRY_LAKE_VERSION"
printf 'PSC_CLASS_A_LITERAL_ENTRY_CACHE_POLICY\tfresh-pinned-dependencies\tupstream-source-hash-cache\tno-local-artifacts\n'
psc_literal_entry_check_sources_and_pins() {
    python3 - "$PSC_LITERAL_ENTRY_ROOT" "$PSC_LITERAL_ENTRY_TMP" "$1" <<'PY'
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
print("PSC_CLASS_A_LITERAL_ENTRY_SOURCE_RECHECK", sys.argv[3], len(manifest),
      hashlib.sha256(encoded).hexdigest(), sep="\t")
if sys.argv[3] == "after-audit":
    for relative, digest in sorted(manifest.items()):
        print("PSC_CLASS_A_LITERAL_ENTRY_SOURCE_AFTER", relative, digest, sep="\t")
PY
}
elan run "$PSC_LITERAL_ENTRY_PIN" lake --no-cache env true
psc_literal_entry_check_sources_and_pins after-clone
elan run "$PSC_LITERAL_ENTRY_PIN" lake --no-cache exe cache get
psc_literal_entry_check_sources_and_pins after-upstream-cache
# These three final targets compile all six new modules through their actual imports.
elan run "$PSC_LITERAL_ENTRY_PIN" lake --no-cache build \
    PscVerif.ClassAMinusCentralBridge PscVerif.ClassAMinusDensity PscVerif.ClassAMinusRootSpectrum
psc_literal_entry_check_sources_and_pins after-build
elan run "$PSC_LITERAL_ENTRY_PIN" lake --no-cache env lean ClassAMinusLiteralEntryAudit.lean \
    | tee "$PSC_LITERAL_ENTRY_TMP/audit.log"
python3 - "$PSC_LITERAL_ENTRY_TMP/audit.log" <<'PY'
from pathlib import Path
import re
import sys

prefix = "PSC_CLASS_A_LITERAL_ENTRY"
# Pinned compiler-owned totals include generated auxiliary declarations. A source
# change must deliberately update these counts alongside its semantic audit.
expected_modules = {
    "PscVerif.ClassAMinusLiteralArithmetic": (34, 26),
    "PscVerif.ClassAMinusNoHalfUnit": (22, 20),
    "PscVerif.ClassAMinusDensity": (31, 31),
    "PscVerif.ClassAMinusPrefixAssembly": (81, 43),
    "PscVerif.ClassAMinusCentralBridge": (71, 42),
    "PscVerif.ClassAMinusRootSpectrum": (13, 12),
}
expected_endpoints = {
    "Psc.ClassAMinusLiteralArithmetic.root_exists",
    "Psc.ClassAMinusLiteralArithmetic.literal_length_scaling",
    "Psc.ClassAMinusLiteralArithmetic.root_coefficient_parameters",
    "Psc.ClassAMinusLiteralArithmetic.constant_amplitude_run_bound",
    "Psc.ClassAMinusNoHalfUnit.physical_abs_ne_half",
    "Psc.ClassAMinusDensity.literal_counts",
    "Psc.ClassAMinusDensity.literal_one_level_density",
    "Psc.ClassAMinusDensity.literal_density_reserve",
    "Psc.ClassAMinusDensity.short_interval_packing",
    "Psc.ClassAMinusDensity.literal_center_count_contradiction",
    "Psc.ClassAMinusDensity.density_threshold_exists",
    "Psc.ClassAMinusPrefixAssembly.ordered_path_original_prefixes",
    "Psc.ClassAMinusPrefixAssembly.ordered_path_zero_original_prefixes",
    "Psc.ClassAMinusPrefixAssembly.OrderedPath.trans",
    "Psc.ClassAMinusCentralBridge.literal_central_composable_path",
    "Psc.ClassAMinusCentralBridge.literal_central_original_prefixes",
    "Psc.ClassAMinusCentralBridge.source_with_central_descendant",
    "Psc.ClassAMinusCentralBridge.invalid_parameters_control",
    "Psc.ClassAMinusPrefixAssembly.incomplete_prefix_control",
    "Psc.ClassAMinusPrefixAssembly.noncomposable_paths_control",
    "Psc.ClassAMinusPrefixAssembly.empty_transcript_control",
    "Psc.ClassAMinusPrefixAssembly.mixed_letter_zero_control",
    "Psc.ClassAMinusDensity.length_two_packing_control",
    "Psc.ClassAMinusRootSpectrum.literal_charpoly",
    "Psc.ClassAMinusRootSpectrum.literal_positive_eigenrow",
    "Psc.ClassAMinusRootSpectrum.literal_other_roots",
    "Psc.ClassAMinusRootSpectrum.literal_pisot_root_exists",
    "Psc.ClassAMinusPrefixAssembly.ordered_path_traced_original_prefixes",
    "Psc.ClassAMinusPrefixAssembly.ordered_path_traced_zero_original_prefixes",
    "Psc.ClassAMinusPrefixAssembly.ordered_path_indexed_interior",
    "Psc.ClassAMinusPrefixAssembly.wrong_transcript_control",
    "Psc.ClassAMinusCentralBridge.literal_central_traced_prefixes",
    "Psc.ClassAMinusCentralBridge.source_with_traced_central_descendant",
}
if len(expected_modules) != 6 or len(expected_endpoints) != 33:
    raise SystemExit("invalid gate's expected literal-entry interface")
rows = [line.split("\t") for line in Path(sys.argv[1]).read_text().splitlines()]
receipts = [row for row in rows if any(prefix in field for field in row)]
expected_tags = ([prefix+"_MODULE"]*6 + [prefix+"_DECLARATIONS"] +
                 [prefix+"_ENDPOINT"]*33 + [prefix+"_AUDIT_COMPLETE"])
if [row[0] for row in receipts] != expected_tags:
    raise SystemExit("missing, duplicate, unexpected or reordered literal-entry receipt")
modules = receipts[:6]
seen_modules = {}
for row in modules:
    if len(row) != 4 or row[1] in seen_modules:
        raise SystemExit("malformed or duplicate owned-module receipt")
    if any(not re.fullmatch(r"[1-9][0-9]*", value) for value in row[2:]):
        raise SystemExit("empty or malformed owned-declaration counts")
    counts = tuple(map(int, row[2:]))
    if counts[1] > counts[0]:
        raise SystemExit("more proof declarations than owned declarations")
    seen_modules[row[1]] = counts
if seen_modules != expected_modules:
    raise SystemExit("missing, extra or wrong-count compiled owned module")
declarations = sum(counts[0] for counts in seen_modules.values())
proofs = sum(counts[1] for counts in seen_modules.values())
if (declarations, proofs) != (252, 174):
    raise SystemExit("unexpected total owned-declaration counts")
if receipts[6] != [prefix+"_DECLARATIONS", "6", str(declarations), str(proofs)]:
    raise SystemExit("inconsistent owned-declaration completion receipt")
endpoint_rows = receipts[7:-1]
if any(len(row) != 2 for row in endpoint_rows):
    raise SystemExit("malformed exact-type endpoint receipt")
found = [row[1] for row in endpoint_rows]
if len(found) != 33 or len(set(found)) != 33 or set(found) != expected_endpoints:
    raise SystemExit("missing, duplicate or unexpected exact-type Lean endpoint")
if receipts[-1] != [prefix+"_AUDIT_COMPLETE", "33", "99"]:
    raise SystemExit("missing or incorrect three-controls-per-endpoint completion receipt")

PY
psc_literal_entry_check_sources_and_pins after-audit
printf 'PSC_CLASS_A_LITERAL_ENTRY_GATE_COMPLETE\t6\t252\t174\t33\t99\n'
