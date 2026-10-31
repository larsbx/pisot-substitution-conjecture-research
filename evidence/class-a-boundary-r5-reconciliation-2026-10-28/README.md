# PR #380 reconciliation after B5 joined #379

Merge R5 head fbf2fcdad44a3315ce7d16cfe28198ae34582948 with updated
parent #379 at 8291fc59144c6445013d493de516b8990ffbdeac, which includes
B5 through #381. The only content conflict was two independent appends to
`docs/side-notes-ledger.md`. Preserve the updated parent ledger as prefix,
then both unchanged R5 entries, then the dated reconciliation note.

Every original R5 packet file is byte-identical to its old head; every B5
packet file is byte-identical to the updated parent. Both original evidence
archives and source digests remain unchanged. No kernel, derivation, proof
status or formal source changes. R5 and B5 registry counts retain their
explicit separate scopes inherited from #379; no combined inventory is
claimed by this conflict repair.

Fresh replay on the reconciled tree:

- `python-scoped.log`: 41 scoped R5/B5/Y4/R4/B4/B3/R3 tests pass.
- `r5-native.log`: locked canonical R5 regression passes, final contract reached.
- `b5-native.log`: locked canonical B5 regression passes, final contract reached.
- `provenance.log`: full provenance verification passes.
- `checksums.log`: both packets' original source and evidence digests pass.

Commands from the repository root:

```sh
python -m pytest -o addopts='' -q tests/test_class_a_boundary_r5_children.py tests/test_class_a_boundary_b5_children.py tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
/root/.pixi/bin/pixi run --locked --manifest-path kernel/pixi.toml mojo run -I kernel kernel/tests/test_class_a_boundary_r5_children.mojo
/root/.pixi/bin/pixi run --locked --manifest-path kernel/pixi.toml mojo run -I kernel kernel/tests/test_class_a_boundary_b5_children.mojo
bash tools/verify_all.sh provenance
sha256sum -c evidence/class-a-boundary-r5-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-r5-2026-10-28/SHA256SUMS
sha256sum -c evidence/class-a-boundary-b5-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-b5-2026-10-28/SHA256SUMS
```

Formal sources are unchanged; previous TLA receipts and precompilation Lean
failure remain historical receipts, not fresh formal runs. This repair
provides no hosted acceptance or mathematical promotion. Exact-head hosted
gates and dependency order remain required before integration.
