# E6 exact packet receipts

Base: #379 head 8291fc59144c6445013d493de516b8990ffbdeac after the observed
merge of #381. This is a stack merge, not main integration or a new proof pass.
Its fresh workflows were queued/pending; exact-head acceptance remains required.

Two complete E6 oriented stars, 2d-1 occurrences each, have the same 16-label
image in every member. Every label has a uniform typed tail <=8, and every
actual first choice has a selected full walk <=9. Nine is attained at n=3;
E6's own uniform exit remains two. J6/K6/L6 gain exits without complete stars.
The n=3 E6/K6/B5 cycle and uniform image/S41 escapes remain actual edges.

Locked Mojo 1.1.0.dev2026090805: 56 members / 82096 pairs / 3136 accepted /
1240 selected path edges / 12664 all-child walk edges. Independent literal-
word/Fraction oracle: 117 / 297648 / 8658 / 2582 / 34766. Every member's
image is checked; all 81 source/image/B5-image registry rows agree.
Forty-three scoped Python tests pass across E6 and its preceding six packets.
The 150 integrity/governance tests also pass.

Replay from repository root:

```sh
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_e6_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_e6_children.mojo
python -m pytest -q tests/test_class_a_boundary_e6_children.py
python oracles/python/class_a_boundary_e6_children.py > /tmp/e6.json
cmp /tmp/e6.json evidence/class-a-boundary-e6-2026-10-28/probe.json
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_e6_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('evidence/class-a-boundary-e6-2026-10-28/driver.log').read_text())"
sha256sum -c evidence/class-a-boundary-e6-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-e6-2026-10-28/SHA256SUMS
```

Finite replays validate implementation; universal nine-kind inequalities,
memberwise label attainment and uniform tail bounds are derived in the companion
note. Independent sign budget 512 refuses inconclusively on exhaustion.
All 18 TLA expected outcomes pass; local Lean fails before compilation and
is not credited. No full local suite or hosted acceptance is claimed.
Independent human review remains pending validation debt. No governed status,
formal source or named-proof inventory changes. No merge pending acceptance.
