# W9 exact replay packet

Provisional base: open #395 at324c167a4f19e7e4b1ec174ee4ef27229654a831.
Observed exact-head hosted runs were queued; no fresh acceptance or main
integration is inferred. Preserve every predecessor packet unchanged.

W9=(x,x,1,3,-5) and reversal have4n+1 indexed children each and the same
16-label image in every member. All16 labels have uniform exits; every actual
first choice has a selected full completion within six edges, attained in
every member. Keep the source's four-edge exit. Six new image companions
have exits3/3/2/5/3/2; no companion stars or forward closure is supplied.

Native replay:56 members/82096 literal pairs/4368 accepted,
448 source-path edges/2016 companion edges/15568 all-child walk edges/
2576 image-tail edges. Independent replay:117/297648/12402,
936/4212/43992/5382. Both verify the entire constant image in every member,
actual reversals, every typed intermediate edge and max six. All91 native
registry rows agree independently. Universal nine-kind/count/member-witness/
path arguments are separate from finite replay in the companion derivation.

All103 scoped Python tests and all157 integrity/source/proof-bank/governance
tests pass. Provenance and digest checks pass. From repository root, with locked native
dependencies and Python dev tools:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_w9_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_w9_children.mojo > /tmp/w9-native-driver.log
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_w9_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('/tmp/w9-native-driver.log').read_text())"
python oracles/python/class_a_boundary_w9_children.py > /tmp/w9.json
cmp /tmp/w9.json evidence/class-a-boundary-w9-2026-10-29/probe.json
python -m pytest -o addopts='' -q tests/test_class_a_boundary_w9_children.py tests/test_class_a_boundary_h9_children.py tests/test_class_a_boundary_p9_children.py tests/test_class_a_boundary_j9_children.py tests/test_class_a_boundary_j8_children.py tests/test_class_a_boundary_d0_children.py tests/test_class_a_boundary_e7_children.py tests/test_class_a_boundary_e6_children.py tests/test_class_a_boundary_b5_children.py tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python -m pytest -o addopts='' -q tests/test_recorded_data_integrity.py tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_claim_governance.py
./tools/verify_all.sh provenance
sha256sum -c evidence/class-a-boundary-w9-2026-10-29/source-sha256.txt
sha256sum -c evidence/class-a-boundary-w9-2026-10-29/SHA256SUMS
```

The X2/Y2 nominal direct RR(1,3) terminal has actual LAST c at n=3,
producing unequal-type (y,c,0,0,0), not a typed coincidence. Keep their
uniform three-edge Y4 paths. X3/Y3 use top RUN n-1; ordinal n is actual
LAST c for y but RUN y for x. Equal offsets do not identify these sources.
The contract also rejects invalid/duplicate/missing/wrong-target packets,
malformed typed terminals, corrupt identities, unknown tails and count
overflow before allocation, including a case where A still fits.

Telemetry and crash reporting are disabled throughout native/hosted replay.
Independent rational sign refinement has inherited budget512 and refuses
inconclusively. Checked native arithmetic refuses overflow. No full local
suite or fresh hosted acceptance is claimed.

No formal/generated/governed changes. Earlier
[TLA outcomes](../class-a-boundary-p9-2026-10-29/tla.log) and
[Lean pre-compilation failure](../class-a-boundary-p9-2026-10-29/lean-attempt.log)
remain dependency receipts; no fresh TLA run or Lean pass is claimed.
No closed carrier, every-continuation termination or global BH/PSC promotion.
Required predecessor and exact-head gates remain outstanding; no merge.
Independent human review stays separate validation debt.
