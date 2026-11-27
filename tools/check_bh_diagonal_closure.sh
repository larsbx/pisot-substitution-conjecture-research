#!/usr/bin/env bash
# Fresh local proof objects over verified pinned dependency sources/caches.
# Set PSC_DIAGONAL_CLOSURE_EVIDENCE_DIR to an empty persistent receipt directory.
# PSC_MOJO may name an executable wrapper for the locked Mojo environment.
set -euo pipefail

# Supported SDK opt-outs keep verification local, including crash reporting.
# https://mojolang.static.modular.com/nightly/docs/faq/
# https://mojolang.static.modular.com/releases/v1.0.0/
export MODULAR_TELEMETRY_ENABLED=false
export MODULAR_CRASH_REPORTING_ENABLED=false

PSC_CLOSURE_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
PSC_CLOSURE_TMP=$(mktemp -d)
trap 'rm -rf "$PSC_CLOSURE_TMP"' EXIT
PSC_CLOSURE_OUT=${PSC_DIAGONAL_CLOSURE_EVIDENCE_DIR:-"$PSC_CLOSURE_TMP/receipts"}
PSC_CLOSURE_MOJO=${PSC_MOJO:-mojo}
mkdir -p "$PSC_CLOSURE_OUT"
if [[ -n "$(ls -A "$PSC_CLOSURE_OUT")" ]]; then
    echo "Evidence directory must be empty; existing receipts are preserved" >&2
    exit 1
fi
PSC_CLOSURE_OUT=$(cd "$PSC_CLOSURE_OUT" && pwd -P)
printf '%s\n' 'MODULAR_TELEMETRY_ENABLED=false' 'MODULAR_CRASH_REPORTING_ENABLED=false' \
    > "$PSC_CLOSURE_OUT/telemetry-policy.log"
PSC_CLOSURE_FRESH="$PSC_CLOSURE_TMP/proof/PscVerif"
PSC_CLOSURE_MODULES=(
    PscVerif.BHDiagonalAllSources
    PscVerif.BHDiagonalClassificationFull
    PscVerif.BHDiagonalConsequences
    PscVerif.BHDiagonalOuter
    PscVerif.BHDiagonalParameters
    PscVerif.BHDiagonalPisot
    PscVerif.BHDiagonalProgress
    PscVerif.BHDiagonalTermination
    PscVerif.BHNearDiagonalPisot
    PscVerif.BHThirdLevelEntry
    PscVerif.BHThirdLevelGeometry
    PscVerif.BHThirdLevelTransport
    PscVerif.BHThreeBandClosure
    PscVerif.BHPisotFiniteBPA
    PscVerif.BHThreeBandBPA
    PscVerif.BHHigherDeterminantPisot
    PscVerif.GeometricFLength
    PscVerif.GeometricFPisotCore
)
printf '%s\n' "${PSC_CLOSURE_MODULES[@]}" > "$PSC_CLOSURE_OUT/module-list.txt"

# Bind the entire tracked/unignored source tree. Runtime receipts themselves
# are excluded only when the caller deliberately puts them inside that tree.
psc_closure_bindings() {
    python3 - "$PSC_CLOSURE_ROOT" "$PSC_CLOSURE_OUT" <<'PY'
import hashlib, json, os, pathlib, subprocess, sys
root = pathlib.Path(sys.argv[1])
receipts = pathlib.Path(sys.argv[2])
listed = subprocess.check_output([
    'git', '-C', str(root), 'ls-files', '--cached', '--others', '--exclude-standard', '-z',
])
bindings = {}
for item in sorted(set(filter(None, listed.split(b'\0')))):
    relative = os.fsdecode(item)
    path = root / relative
    if path.resolve().is_relative_to(receipts):
        continue
    if path.is_symlink():
        raise SystemExit('source symlink is not accepted: ' + relative)
    if not path.is_file():
        raise SystemExit('source file is missing: ' + relative)
    bindings[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
print(json.dumps(bindings, indent=2, sort_keys=True))
PY
}

psc_closure_bindings > "$PSC_CLOSURE_OUT/source-bindings.json"
git -C "$PSC_CLOSURE_ROOT" rev-parse HEAD 'HEAD^{tree}' > "$PSC_CLOSURE_OUT/revision.txt"
python3 "$PSC_CLOSURE_ROOT/tools/make_proof_bank.py" --check \
    --prepare-audit-workspace "$PSC_CLOSURE_FRESH" \
    > "$PSC_CLOSURE_OUT/proof-bank-check.log" 2>&1
python3 "$PSC_CLOSURE_ROOT/tools/make_proof_bank.py" --pins-only --require-packages \
    > "$PSC_CLOSURE_OUT/dependency-pins-before.json"
mkdir -p "$PSC_CLOSURE_FRESH/.lake"
ln -s "$PSC_CLOSURE_ROOT/proof/PscVerif/.lake/packages" "$PSC_CLOSURE_FRESH/.lake/packages"

psc_closure_check_copied_sources() {
    python3 - "$PSC_CLOSURE_OUT/source-bindings.json" "$PSC_CLOSURE_FRESH" "$1" <<'PY'
import hashlib, json, pathlib, sys
bindings = json.loads(pathlib.Path(sys.argv[1]).read_text())
fresh = pathlib.Path(sys.argv[2])
prefix = 'proof/PscVerif/'
config = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}
expected = {
    path[len(prefix):]: digest for path, digest in bindings.items()
    if path.startswith(prefix) and
       (path.endswith('.lean') or path[len(prefix):] in config)
}
paths = [fresh / name for name in config]
paths += sorted(fresh.glob('*.lean')) + sorted((fresh / 'PscVerif').rglob('*.lean'))
actual = {p.relative_to(fresh).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in paths}
if actual != expected:
    raise SystemExit('fresh project source/pin mismatch at ' + sys.argv[3])
encoded = json.dumps(expected, sort_keys=True, separators=(',', ':')).encode()
print('PSC_BH_DIAGONAL_CLOSURE_SOURCE_COPY', sys.argv[3], len(expected),
      hashlib.sha256(encoded).hexdigest(), sep='\t')
PY
}
psc_closure_check_copied_sources before-build > "$PSC_CLOSURE_OUT/source-copy-checks.log"

# Inherited paths and artifact caches must not supply local project objects.
for PSC_CLOSURE_ENV in "${!LEAN_@}" "${!LAKE_@}" "${!MATHLIB_CACHE_@}"; do
    if [[ -n "$PSC_CLOSURE_ENV" ]]; then unset "$PSC_CLOSURE_ENV"; fi
done
unset PYTHONPATH PYTHONHOME
export LAKE_CONFIG="" LAKE_CACHE_DIR="" LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false
export PYTEST_DISABLE_PLUGIN_AUTOLOAD=1
cd "$PSC_CLOSURE_FRESH"
PSC_CLOSURE_PIN=$(cat lean-toolchain)
PSC_CLOSURE_RELEASE=${PSC_CLOSURE_PIN#leanprover/lean4:v}
if command -v elan >/dev/null 2>&1; then
    PSC_CLOSURE_LEAN=(elan run "$PSC_CLOSURE_PIN" lean)
    PSC_CLOSURE_LAKE=(elan run "$PSC_CLOSURE_PIN" lake)
else
    PSC_CLOSURE_LEAN=("$(command -v lean)")
    PSC_CLOSURE_LAKE=("$(command -v lake)")
fi
PSC_CLOSURE_LEAN_VERSION=$("${PSC_CLOSURE_LEAN[@]}" --version)
PSC_CLOSURE_LAKE_VERSION=$("${PSC_CLOSURE_LAKE[@]}" --version)
if [[ "$PSC_CLOSURE_LEAN_VERSION" != "Lean (version $PSC_CLOSURE_RELEASE,"* ]] \
   || [[ "$PSC_CLOSURE_LAKE_VERSION" != *"(Lean version $PSC_CLOSURE_RELEASE)" ]]; then
    echo "Lean/Lake executable does not match the repository pin" >&2
    exit 1
fi
printf '%s\n%s\n' "$PSC_CLOSURE_LEAN_VERSION" "$PSC_CLOSURE_LAKE_VERSION" \
    > "$PSC_CLOSURE_OUT/versions.log"
"$PSC_CLOSURE_MOJO" --version >> "$PSC_CLOSURE_OUT/versions.log"
python3 --version >> "$PSC_CLOSURE_OUT/versions.log"
python3 - "$PSC_CLOSURE_ROOT/kernel/pixi.lock" "$PSC_CLOSURE_OUT/versions.log" <<'PY'
import pathlib, re, sys
lock = pathlib.Path(sys.argv[1]).read_text()
versions = set(re.findall(r'/mojo-compiler-([0-9][A-Za-z0-9.+]*)-release\.conda', lock))
if len(versions) != 1:
    raise SystemExit('expected exactly one pinned Mojo compiler version')
version = versions.pop()
lines = pathlib.Path(sys.argv[2]).read_text().splitlines()
if not any(line.startswith('Mojo ' + version + ' ') for line in lines):
    raise SystemExit('Mojo executable does not match kernel/pixi.lock')
PY
printf '%s\n' 'PSC_BH_DIAGONAL_CLOSURE_CACHE_POLICY	verified-pinned-dependency-cache	fresh-project-objects' \
    > "$PSC_CLOSURE_OUT/cache-policy.log"
if [[ -e .lake/build ]]; then
    echo "Unexpected project build artifacts before fresh compilation" >&2
    exit 1
fi
"${PSC_CLOSURE_LAKE[@]}" --no-cache build "${PSC_CLOSURE_MODULES[@]}" \
    PscVerif.BHDiagonalCertificate > "$PSC_CLOSURE_OUT/lean-build.log" 2>&1
psc_closure_check_copied_sources after-build >> "$PSC_CLOSURE_OUT/source-copy-checks.log"
"${PSC_CLOSURE_LAKE[@]}" --no-cache env lean BHDiagonalClosureAudit.lean \
    > "$PSC_CLOSURE_OUT/lean-audit.log" 2>&1
"${PSC_CLOSURE_LAKE[@]}" --no-cache env lean BHDiagonalResidualAudit.lean \
    > "$PSC_CLOSURE_OUT/residual-audit.log" 2>&1
"${PSC_CLOSURE_LAKE[@]}" --no-cache env lean BHDiagonalLiteralAudit.lean \
    > "$PSC_CLOSURE_OUT/literal-audit.log" 2>&1
"${PSC_CLOSURE_LAKE[@]}" --no-cache env lean BHNearDiagonalAudit.lean \
    > "$PSC_CLOSURE_OUT/near-diagonal-audit.log" 2>&1
psc_closure_check_copied_sources after-audit >> "$PSC_CLOSURE_OUT/source-copy-checks.log"

# Match the exact module list and all declared endpoint receipts, rejecting
# duplicates, omissions and incomplete audits rather than trusting exit code alone.
python3 - "$PSC_CLOSURE_FRESH/BHDiagonalClosureAudit.lean" "$PSC_CLOSURE_OUT" <<'PY'
import json, pathlib, re, sys
source = pathlib.Path(sys.argv[1]).read_text()
out = pathlib.Path(sys.argv[2])
def declared(name):
    match = re.search(r'let ' + name + r' := #\[(.*?)\]', source, re.S)
    if match is None:
        raise SystemExit('missing explicit audit list: ' + name)
    values = re.findall(r'`([A-Za-z_][A-Za-z0-9_.]*)', match[1])
    if not values or len(values) != len(set(values)):
        raise SystemExit('empty or duplicate audit list: ' + name)
    return values
endpoints, modules = declared('endpoints'), declared('modules')
if modules != (out / 'module-list.txt').read_text().splitlines():
    raise SystemExit('gate module list differs from compiled audit list')
lines = (out / 'lean-audit.log').read_text().splitlines()
endpoint_rows = [row.split('\t')[1:] for row in lines
                 if row.startswith('PSC_BH_DIAGONAL_CLOSURE_ENDPOINT\t')]
module_rows = [row.split('\t')[1:] for row in lines
               if row.startswith('PSC_BH_DIAGONAL_CLOSURE_MODULE\t')]
if endpoint_rows != [[name] for name in endpoints]:
    raise SystemExit('compiled endpoint receipt mismatch')
if [row[0] for row in module_rows] != modules or any(len(row) != 3 for row in module_rows):
    raise SystemExit('compiled module receipt mismatch')
counts = [(int(row[1]), int(row[2])) for row in module_rows]
if any(not 0 < theorems <= declarations for declarations, theorems in counts):
    raise SystemExit('empty or inconsistent compiled module counts')
complete = f'PSC_BH_DIAGONAL_CLOSURE_AUDIT_COMPLETE\t{len(endpoints)}\t{len(modules)}'
if lines.count(complete) != 1:
    raise SystemExit('closure audit completion receipt mismatch')
residual = (out / 'residual-audit.log').read_text().splitlines()
if residual.count('PSC_BH_DIAGONAL_AUDIT_COMPLETE\t18\t6') != 1:
    raise SystemExit('inherited residual audit did not complete')
for filename, prefix in [('literal-audit.log', 'PSC_BH_DIAGONAL_LITERAL_AUDIT\t'),
                         ('near-diagonal-audit.log', 'PSC_BH_NEAR_DIAGONAL_AUDIT\t')]:
    if sum(line.startswith(prefix) for line in (out / filename).read_text().splitlines()) != 2:
        raise SystemExit('inherited literal audit did not complete: ' + filename)
(out / 'lean-summary.json').write_text(json.dumps({
    'status': 'passed', 'modules': modules, 'endpoints': endpoints,
    'declarations': sum(pair[0] for pair in counts),
    'theorems': sum(pair[1] for pair in counts),
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'local_objects': 'freshly built from byte-matched isolated project sources',
    'dependency_objects': 'cached; pinned dependency source bytes verified before and after',
}, indent=2) + '\n')
PY

cd "$PSC_CLOSURE_ROOT/kernel"
"$PSC_CLOSURE_MOJO" run -I . -I tests tests/test_bh_diagonal_residual.mojo \
    > "$PSC_CLOSURE_OUT/native-residual-test.log" 2>&1
"$PSC_CLOSURE_MOJO" run -I . -I tests tests/test_bh_third_level_windows.mojo \
    > "$PSC_CLOSURE_OUT/native-third-level-test.log" 2>&1
"$PSC_CLOSURE_MOJO" run -I . bh_diagonal_residual.mojo \
    > "$PSC_CLOSURE_OUT/residual-certificates.csv" 2> "$PSC_CLOSURE_OUT/native-export.log"
cd "$PSC_CLOSURE_ROOT"
python3 oracles/python/bh_diagonal_residual.py \
    --native-csv "$PSC_CLOSURE_OUT/residual-certificates.csv" \
    > "$PSC_CLOSURE_OUT/independent-oracle.json"
python3 -m pytest -o addopts='' -q tests/test_bh_diagonal_residual_oracle.py \
    > "$PSC_CLOSURE_OUT/oracle-controls.log" 2>&1
python3 "$PSC_CLOSURE_ROOT/tools/make_proof_bank.py" --pins-only --require-packages \
    > "$PSC_CLOSURE_OUT/dependency-pins-after.json"
cmp "$PSC_CLOSURE_OUT/dependency-pins-before.json" "$PSC_CLOSURE_OUT/dependency-pins-after.json"
psc_closure_check_copied_sources after-native-replay >> "$PSC_CLOSURE_OUT/source-copy-checks.log"
psc_closure_bindings > "$PSC_CLOSURE_OUT/source-bindings-after.json"
cmp "$PSC_CLOSURE_OUT/source-bindings.json" "$PSC_CLOSURE_OUT/source-bindings-after.json"

python3 - "$PSC_CLOSURE_OUT" <<'PY'
import hashlib, json, pathlib, sys
out = pathlib.Path(sys.argv[1])
for filename, terminal in [
    ('native-residual-test.log', 'exact finite residual certificates:'),
    ('native-third-level-test.log', 'exact third-level choices and the two original digit triples verified'),
]:
    lines = (out / filename).read_text().splitlines()
    if not any(line.startswith(terminal) for line in lines):
        raise SystemExit('missing native terminal receipt: ' + filename)
    if sum(line.startswith('contract-receipt: ') for line in lines) != 1:
        raise SystemExit('missing or duplicate native contract receipt: ' + filename)
oracle = json.loads((out / 'independent-oracle.json').read_text())
native_hash = hashlib.sha256((out / 'residual-certificates.csv').read_bytes()).hexdigest()
if oracle.get('status') != 'passed' or oracle.get('native_sha256') != native_hash:
    raise SystemExit('independent oracle did not certify this native export')
if [row['r'] for row in oracle['parameters']] != [12, 13, 15, 16, 18, 20, 32]:
    raise SystemExit('independent oracle parameter scope changed')
lean = json.loads((out / 'lean-summary.json').read_text())
bindings = (out / 'source-bindings.json').read_bytes()
summary = {
    'status': 'passed',
    'lean_scope': {
        'literal_exits_coincidence_finite_bpa': 'all natural r >= 12 and r <= k <= r+2',
        'primitive_irreducible_pisot_arithmetic': 'all natural 4 <= r <= k',
        'contracts': 'exact compiled endpoint signatures; no spectral dynamical axiom',
    },
    'native_scope': 'finite parameters and declared source packets only; not the uniform proof',
    'modules': len(lean['modules']), 'endpoints': len(lean['endpoints']),
    'declarations': lean['declarations'], 'theorems': lean['theorems'],
    'source_inputs': len(json.loads(bindings)),
    'source_bindings_sha256': hashlib.sha256(bindings).hexdigest(),
    'sources_unchanged': True,
    'native_export_sha256': native_hash,
    'finite_square_states': oracle['total_square_states'],
    'finite_disk_pairs': oracle['total_disk_pairs'],
}
(out / 'gate-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('PSC_BH_DIAGONAL_CLOSURE_GATE_COMPLETE', summary['modules'], summary['endpoints'],
      summary['declarations'], summary['theorems'], summary['source_inputs'], sep='\t')
PY
