# B5 exact packet receipts

Based independently on PR #379 at 7eb395cce20973c2c36bef09c97b3d6ae8e57067.
Concurrent unfinished R5 changes were left untouched in another checkout.
The complete R5 star is not a dependency: #379's R5 source and selected exit
suffice to certify the actual B5 ancestry directly.

Canonical scoped regression: exit 0, locked Mojo 1.1.0.dev2026090805;
56 members, 33096 pairs, 2016 accepted, 460 selected path edges,
11266 all-child walk edges, maximum eight. Independent replay: 117 members,
122616 pairs, 5850 accepted, 948 selected edges, 34884 all-child edges.
Both attain all 24 labels. All 65 source/image registry rows agree.
Thirty-five scoped Python tests and 149 integrity/governance tests pass.

E7 endpoint tails apply only at n=4: (k,t)=(1,0),(0,1). No uniform E7
exit or companion complete star is registered. Actual first-choice walks
are completely covered, including the n=3 E6 endpoint. The independent
512-refinement sign budget refuses on exhaustion.

Replay from repository root:

```sh
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_b5_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_b5_children.mojo
python -m pytest -q tests/test_class_a_boundary_b5_children.py
python oracles/python/class_a_boundary_b5_children.py > /tmp/b5.json
cmp /tmp/b5.json evidence/class-a-boundary-b5-2026-10-28/probe.json
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_b5_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('evidence/class-a-boundary-b5-2026-10-28/driver.log').read_text())"
sha256sum -c evidence/class-a-boundary-b5-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-b5-2026-10-28/SHA256SUMS
```

Scoped Python command covers B5, Y4, R4, B4, B3 and R3 regressions. Formal
attempts and provenance receipts remain separate. All 18 TLA expected
outcomes pass; Lean fails before compilation and earns no pass. Full local
native/Python suites are not claimed. Fresh predecessor and exact-head hosted
acceptance remain required before integration. No formal source or governed
status changes. Independent human review remains pending validation debt.
