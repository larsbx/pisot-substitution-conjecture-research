# H9 exact replay packet

Base #391 merge revision65e7b8a8724b9e3f4f6f0ec2f230b3dada4993ca
incorporates #393. Observed merge-head workflows were queued. No fresh
acceptance, main integration or independent sibling result is inferred.
Every predecessor packet remains unchanged.

H9=(x,x,1,3,-6) and actual reversal have complete indexed stars:
2A+3 at k=0,1 and2A-2k+5 at k>=2. Their chamber-wide image has20 labels,
all with uniform exits. Every actual first choice admits a selected full
completion within seven edges, attained. The existing source exit stays six.
K9/L9/M9 gain uniform four/three/six-edge exits, with no companion stars.

FF and LL have equal full targets but distinct indices. Do not deduplicate
them by label. All arbitrary image-source tails have at most seven edges;
actual H9-child tails have at most six because D4 ancestry requires k>=2,
where its short suffix applies. Preserve D4's seven-edge n=3 tail unchanged.
No every-continuation termination, forward closure, closed obstruction or
global BH/PSC conclusion.

Native replay:56 members/82096 literal pairs/5124 accepted children,
672 source-path edges,1456 companion edges,30366 all-child walk edges,
4404 full-image tail edges. Independent replay:117/297648/13302,
1404/3042/78714/9170. Both attain all20 labels and max7, with actual
reversals and every typed intermediate edge checked. All93 native registry
rows match the independent interface. Universal nine-kind/count/path
arguments are separate from finite implementation replay in the derivation.

All 94 scoped Python tests and all 156 integrity/source/proof-bank/governance
tests pass. Provenance and source/packet digests pass.

From repository root, with locked native dependencies and Python dev tools:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_h9_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_h9_children.mojo > /tmp/h9-native-driver.log
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_h9_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('/tmp/h9-native-driver.log').read_text())"
python oracles/python/class_a_boundary_h9_children.py > /tmp/h9.json
cmp /tmp/h9.json evidence/class-a-boundary-h9-2026-10-29/probe.json
python -m pytest -o addopts='' -q tests/test_class_a_boundary_h9_children.py tests/test_class_a_boundary_p9_children.py tests/test_class_a_boundary_j9_children.py tests/test_class_a_boundary_j8_children.py tests/test_class_a_boundary_d0_children.py tests/test_class_a_boundary_e7_children.py tests/test_class_a_boundary_e6_children.py tests/test_class_a_boundary_b5_children.py tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python -m pytest -o addopts='' -q tests/test_recorded_data_integrity.py tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_claim_governance.py
./tools/verify_all.sh provenance
sha256sum -c evidence/class-a-boundary-h9-2026-10-29/source-sha256.txt
sha256sum -c evidence/class-a-boundary-h9-2026-10-29/SHA256SUMS
```

Every native invocation and hosted job disables telemetry and crash reporting.
Checked arithmetic refuses overflow; a regression refuses 2A+3 overflow
before trying to allocate the star even though A fits. Independent rational
sign refinement has inherited budget512 and refuses inconclusively.

No formal/model/generated/governed source changes. The earlier
[TLA receipt](../class-a-boundary-p9-2026-10-29/tla.log) and
[Lean pre-compilation failure](../class-a-boundary-p9-2026-10-29/lean-attempt.log)
remain dependency receipts; no fresh TLA run or Lean pass is claimed.
No full local suite or fresh hosted acceptance. Required predecessor and
exact-head gates remain outstanding; no merge. Independent human review
remains separate validation debt.
