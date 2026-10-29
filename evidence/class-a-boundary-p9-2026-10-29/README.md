# P9 exact replay packet

Provisional base: open #391, head92e34bea5bffee8a8523eeda40096b453a435377.
The original parent-workflows.json records queued runs. The later
parent-workflows-authorized.json has seven successes including dedicated J9,
two running and seven queued; it is not complete dependency acceptance.
Every predecessor packet is unchanged. No independent sibling result is counted.

For P9=(x,y,-1,-4,7) and actual reversal, complete indexed stars have
2n+2+[k>=2] children and 24 chamber-wide image labels. Every actual first
choice has a selected typed completion within nine edges; nine is attained.
Keep inherited seven/six-edge source exits. New W9/B9 have uniform four/three-
edge exits. X9 and existing L8 tails remain k0-only; only X9's source overlap
is uniform. Twenty image labels have uniform exits and four guarded tails.
No companion complete stars, closed carrier or global BH/PSC claim.

Independent exact replay: 117 members, 234 stars, 122616 literal pairs,
6750 accepted edges, 1422 source-path edges, 1746 companion-path edges,
39618 all-child walk edges. Every image label is witnessed and every actual
reversal/full typed path is checked. Universal guards/counts/path legality
are separately proved in the companion derivation. Sign refinement has
inherited budget512 and refuses inconclusively.

**Authorized native validation passes.** Locked Mojo 1.1.0.dev2026090805
compiles and passes the contract unchanged with telemetry/crash reporting
disabled. The native finite replay checks 56 members, 33096 literal pairs,
2436 accepted edges, 686 source-path edges, 868 companion-path edges and
14322 all-child walk edges; max nine is attained and the contract receipt
is reached. All 107 actual driver rows match the independent interfaces.
See native-tests.log, driver.log, native-version.log and native-registry.log.

Preserve native-attempt.log as the initial automatic-review rejection,
which was followed by explicit user authorization. The initial publication
commit b58ff2c8 used [skip ci] and earned no hosted acceptance. The new
validation commit allows normal hosted checks with both native opt-outs still
set. Fresh exact-head and predecessor gates remain required; no merge.

From repository root:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_p9_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_p9_children.mojo > /tmp/p9-native-driver.log
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_p9_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('/tmp/p9-native-driver.log').read_text())"
```

Independent and governance replay:

```sh
python oracles/python/class_a_boundary_p9_children.py > /tmp/p9.json
cmp /tmp/p9.json evidence/class-a-boundary-p9-2026-10-29/probe.json
python -m pytest -o addopts='' -q tests/test_class_a_boundary_p9_children.py tests/test_class_a_boundary_j9_children.py tests/test_class_a_boundary_j8_children.py tests/test_class_a_boundary_d0_children.py tests/test_class_a_boundary_e7_children.py tests/test_class_a_boundary_e6_children.py tests/test_class_a_boundary_b5_children.py tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python -m pytest -o addopts='' -q tests/test_recorded_data_integrity.py tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_claim_governance.py
./tools/verify_all.sh provenance
TLA_TOOLS=/path/to/tla2tools.jar ./proof/tla/check.sh
./tools/check_lean.sh
sha256sum -c evidence/class-a-boundary-p9-2026-10-29/source-sha256.txt
sha256sum -c evidence/class-a-boundary-p9-2026-10-29/SHA256SUMS
```

Authorized follow-up: all 85 scoped Python tests and all 155 integrity,
source, proof-bank and governance tests pass. Provenance passes; the canonical
Mojo sources and contract were unchanged. Earlier receipts remain intact.
The initial integrity run has 153 passes
and one failure because the new packet did not yet have its digest manifest;
a second run caught the not-yet-staged evidence; the final staged
recorded-data/link/Markdown-source replay passes all 96 checks. The other integrity,
Markdown-source, proof-bank and governance checks remain passed. Provenance
and all 18 TLA expected outcomes pass. Lean still fails before compilation.
No full local suite or fresh hosted pass is claimed. Preserve the governed
claim inventory and formal sources. Independent human review stays separate
validation debt, not a research-progress gate.
