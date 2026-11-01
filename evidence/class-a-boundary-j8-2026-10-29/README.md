# J8 exact replay packet

Base #382 at 526b3dc1ef8dcb914802992a6fee7b3148236c6a has #385 merged.
All17 observed parent workflows passed. This does not establish acceptance
of the new head or main integration. #386 was closed unmerged; restore its
D0 packet unchanged, with exactly its tested tree 799fcce9ad47ad7906905619c8cf88616342df84.
Independent R5/D5/class-C sibling results are not counted. Old D0 receipts and
status descriptions remain historical, not rewritten.

J8/reversal complete stars have 2n+3+[k=0] indexed children and an 18-label
chamber union. Every actual first choice has selected completion <=9, attained.
Source exits take six edges at k=0 and four at k>=1. Reversed L/G5 aliases
reuse their existing certificates. L8 source and path are k=0-only; Z8/D8
paths are k=0/k=1-only, even though those sources are interior elsewhere.
The registry separates two inherited image stars, sixteen uniform image exits,
and two conditional actual-image tails. No companion complete stars are new.

Locked native replay: 56 members / 33,096 pairs / 2,478 accepted edges /
1,274 path cells / 5,656 source-companion path edges / 14,434 all-child walk
edges / 3,690 guarded image-tail edges. Independent replay: 117 / 122,616 /
6,804 / 2,628 / 11,502 / 39,762 / 7,532. Both attain all18 labels and max
walk nine. All119 native registry rows match independently. Restored D0
native replay passes; 67 scoped Python tests pass across J8 and nine preceding
packets. A further 153 integrity/link/proof-bank/governance tests pass.
No full local suite is claimed.

Install the repository dev dependencies before Python replay. From root:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_j8_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_j8_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_d0_children.mojo
python oracles/python/class_a_boundary_j8_children.py > /tmp/j8.json
cmp /tmp/j8.json evidence/class-a-boundary-j8-2026-10-29/probe.json
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_j8_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('evidence/class-a-boundary-j8-2026-10-29/driver.log').read_text())"
python -m pytest -o addopts='' -q tests/test_class_a_boundary_j8_children.py tests/test_class_a_boundary_d0_children.py tests/test_class_a_boundary_e7_children.py tests/test_class_a_boundary_e6_children.py tests/test_class_a_boundary_b5_children.py tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python -m pytest -o addopts='' -q tests/test_recorded_data_integrity.py tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_claim_governance.py
./tools/verify_all.sh provenance
TLA_TOOLS=/path/to/tla2tools.jar ./proof/tla/check.sh
./tools/check_lean.sh
sha256sum -c evidence/class-a-boundary-j8-2026-10-29/source-sha256.txt
sha256sum -c evidence/class-a-boundary-j8-2026-10-29/SHA256SUMS
sha256sum -c evidence/class-a-boundary-d0-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-d0-2026-10-28/SHA256SUMS
```

The native receipt uses locked Mojo. An initial default invocation was
rejected by automatic approval review because it could disclose telemetry;
it earns no receipt. Subsequent successful checks disable telemetry and crash
reporting using the documented environment switches, also set in the new
workflow. Official documentation: https://mojolang.static.modular.com/1.1.0/docs/faq/
and https://mojolang.static.modular.com/releases/v1.0.0/.

Finite replay validates implementation separately from the universal nine-kind,
separator and parameter-region derivation. Sign refinement has budget512 and
refuses inconclusively; canonical machine arithmetic refuses overflow.
Provenance and all18 TLA expected outcomes pass. Lean provisioning and the
isolated proof check fail before compilation, earning no pass. Preserve 124
governed claims, 34 named Lean proofs and 325 source openings. No general E7
all-child, closed carrier, global BH or PSC claim; no merge pending exact-head
gates. Independent human review remains validation debt.
