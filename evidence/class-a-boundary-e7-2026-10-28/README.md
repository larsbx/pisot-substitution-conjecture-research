# E7 exact packet receipts

Base: #382 head 6bef25b0a24820996989f652d53f1ae5d24039c2. Its fresh hosted
workflows were queued at inspection; predecessor and exact-head acceptance
remain required before integration. Independent human review is pending debt.

Two complete E7 oriented stars have max(1,2t-1) indexed occurrences, with a
32-label chamber-wide union and exact alpha=1/2 guard split. Uniform source
exits have lengths 3 at t=0,1 and 5 at t>=2. Only singleton t<=1 stars
receive all-direct-child productivity here. Opposite-chamber disjoint target
labels are not silently declared uniform sources or productive descendants.

U7 is existing reversed D0, and V7 is existing Dxx. Reuse their certificates;
V7 receives a two-edge shortcut only at n>=4, retaining its four-edge path
at n=3. J/H5 complete stars are reused. No new companion stars or uniform
alias claims. The previous B5 image now has uniform tails for all 24 labels.
All 97 candidate/image/B5-image native registry rows agree independently.

Locked Mojo 1.1.0.dev2026090805: 56 members, 82096 literal pairs, 592 accepted,
948 source/companion path edges, 1138 registered-image tail edges, 4704 uniform
B5-image tail edges. Independent replay: 117 / 297648 / 1690 / 2006 / 2362 /
9880. Fifty-one scoped Python tests pass across E7 and seven preceding packets.
A further 151 integrity, link, proof-bank and governance tests pass.

Replay from repository root:

```sh
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_e7_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_e7_children.mojo
python -m pytest -q tests/test_class_a_boundary_e7_children.py
python oracles/python/class_a_boundary_e7_children.py > /tmp/e7.json
cmp /tmp/e7.json evidence/class-a-boundary-e7-2026-10-28/probe.json
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_e7_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('evidence/class-a-boundary-e7-2026-10-28/driver.log').read_text())"
sha256sum -c evidence/class-a-boundary-e7-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-e7-2026-10-28/SHA256SUMS
```

Finite replays validate implementation; the universal nine-kind proof,
separator and exit legality are separate in the companion derivation.
Independent sign budget 512 refuses on exhaustion. All 18 TLA expected
outcomes pass. Local Lean fails before compilation and earns no pass.
No full local suite or fresh hosted acceptance is claimed. No formal source,
governed status or named-proof inventory changes. No merge pending acceptance.
