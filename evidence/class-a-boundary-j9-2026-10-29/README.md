# J9 exact replay packet

Base #382 at d204b822b8912c8d41b7cca22bd7de9770c88e3c merges #387.
Merge-head workflows were initially queued; the latest mixed queued/running/
success snapshot is archived separately and is not exact-head acceptance.
No main integration or independent-sibling result is counted. Preserve every
predecessor packet unchanged.

J9/reversal complete stars have the exact piecewise indexed counts proved in
the companion derivation and a 34-label chamber-wide image. Uniform selected
source exits take eight edges at k=0 and seven at k>=1. P9 has seven/six-edge
exits and H9 a six-edge exit. Only P9/reversal in the image have registered
uniform tails; 32 labels remain unregistered. No all-direct-child productivity,
companion complete stars, closed carrier or global BH conclusion.

Locked native replay: 56 members / 33,096 pairs / 2,130 accepted edges /
336 path cells / 2,156 source-companion path edges / 686 registered image-tail
edges. Independent replay: 117 / 122,616 / 5,390 / 702 / 4,482 / 1,422.
Both attain all 34 labels and verify actual reversals. All 113 native registry
rows match independently. Seventy-five scoped Python tests pass across J9 and
ten preceding packets. A further 154 integrity/link/proof-bank/governance tests
pass. No full local suite is claimed.

Install repository dev dependencies before Python replay. From root:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_j9_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_j9_children.mojo
python oracles/python/class_a_boundary_j9_children.py > /tmp/j9.json
cmp /tmp/j9.json evidence/class-a-boundary-j9-2026-10-29/probe.json
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_j9_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('evidence/class-a-boundary-j9-2026-10-29/driver.log').read_text())"
python -m pytest -o addopts='' -q tests/test_class_a_boundary_j9_children.py tests/test_class_a_boundary_j8_children.py tests/test_class_a_boundary_d0_children.py tests/test_class_a_boundary_e7_children.py tests/test_class_a_boundary_e6_children.py tests/test_class_a_boundary_b5_children.py tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python -m pytest -o addopts='' -q tests/test_recorded_data_integrity.py tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_claim_governance.py
./tools/verify_all.sh provenance
TLA_TOOLS=/path/to/tla2tools.jar ./proof/tla/check.sh
./tools/check_lean.sh
sha256sum -c evidence/class-a-boundary-j9-2026-10-29/source-sha256.txt
sha256sum -c evidence/class-a-boundary-j9-2026-10-29/SHA256SUMS
```

The exact identity beta*(2v-1)=t-k+3-alpha-4h and the auxiliary polynomial
sign at t-k=-2 prove v>1/2 iff t>=k-2, excluding equality. Independent sign
refinement has budget 512 and refuses inconclusively. Canonical machine
arithmetic refuses overflow, including the regression where A fits but the
upper LR bound does not. Finite replay validates implementation separately
from the nine-kind, separator and uniform selected-path arguments.

Provenance and all 18 existing TLA expected outcomes pass. Local Lean fails
before compilation, earning no pass. Native telemetry/crash reporting are
disabled, also in hosted replay. Keep 124 governed claims, 34 named Lean
proofs and 325 source openings unchanged. No merge pending required
predecessor and exact-head gates; independent human review stays validation debt.
