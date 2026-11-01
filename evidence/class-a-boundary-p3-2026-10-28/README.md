# P3 packet receipts

Parent: PR #365, e4f7fc767a45c9445c5294c16d7a703f75f43828.
Scope: six oriented P3/T/U stars, 37-label chamber-wide image, P3 typed exit
within two steps. Universal inequalities are in the companion derivation;
finite output is not their universal quantifier.

Native replay: 56 members, 148288 pairs, 6216 accepted, 448 selected edges.
Independent replay: 117 members, 702 source cells, 542880 pairs,
17316 accepted, 936 selected edges. All 37 labels have actual witnesses.

Commands from repository root:

```sh
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_p3_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_p3_children.mojo
python -m pytest -q tests/test_class_a_boundary_p3_children.py
python oracles/python/class_a_boundary_p3_children.py > /tmp/p3.json
cmp /tmp/p3.json evidence/class-a-boundary-p3-2026-10-28/probe.json
sha256sum -c evidence/class-a-boundary-p3-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-p3-2026-10-28/SHA256SUMS
```

Local Lean fails before compilation and earns no proof pass. No new Lean/TLA
source or governed promotion. Pending exact-head hosted acceptance and
independent human review; no merge. Broader environment attempts and scoped
receipts remain distinct. No forward closure or every-P3-child productivity.
