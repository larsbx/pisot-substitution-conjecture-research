# Finite class-B top-layer label-ray evidence

Canonical native exports live in `labels/`: sorted `(top,bottom,k,c,y,depth)`
records with bottom-minus-top offsets, complete uncapped graphs only.
`witnesses/` adds one legal indexed child of depth one lower per non-target
on plus g=1, q=9,10. The native exporter reconstructs the actual occurrence
pair; the independent rank prototype replays its letters and integer shift.

`carriers.json` records each residue's finite training floor, full typed
interval endpoint coefficients in l, all earlier observed q values, and
separately tested holdouts. Each carrier row is
`[top,bottom,s,d,lo_a,lo_b,hi_a,hi_b]`, where s=3k+c+y, d=c−3k.
Training bounds are exactly the old pilot bounds: plus g=1 q<=26, plus g=2
q<=18, and q<=30 on the other six lines. Holdouts do not choose the floors.
A floor is the earliest successful model in this finite training window,
not a proved stabilization threshold. Prefix labels remain explicit.

`rank-probe.json` preserves a bounded rank synthesis attempt, its refusals,
holdout depth-envelope checks and a real nondecreasing-potential edge.
It is not a rank or boundary-hitting certificate. `inputs.json` pins source
and lock inputs. `SHA256SUMS` pins this entire packet byte-for-byte.

## Replay

From kernel/ with the locked environment:

```
pixi run --locked mojo build -I . class_b_label_rays.mojo -o /tmp/class-b-label-rays
pixi run --locked mojo build -I . class_b_label_fit.mojo -o /tmp/class-b-label-fit
pixi run --locked mojo run -I . tests/test_class_b_label_fit.mojo
```

From repository root:

```
python oracles/python/class_b_label_rays.py evidence/class-b-label-rays-2026-10-23/labels --require-complete --native /tmp/class-b-label-fit --out /tmp/carriers.json
cmp /tmp/carriers.json evidence/class-b-label-rays-2026-10-23/carriers.json
python oracles/python/class_b_label_graph_oracle.py
python oracles/python/class_b_rank_probe.py evidence/class-b-label-rays-2026-10-23/labels /tmp/rank-probe.json
cmp /tmp/rank-probe.json evidence/class-b-label-rays-2026-10-23/rank-probe.json
python oracles/python/class_b_label_replay.py /tmp/class-b-label-rays evidence/class-b-label-rays-2026-10-23 /tmp/class-b-fresh
python -m pytest -q tests/test_class_b_label_rays.py
```

The replay wrapper only invokes the native implementation and compares bytes;
its workers do not implement graph mathematics. The independent graph oracle
reconstructs two complete graphs over Fraction-based Q(beta), not only counts.
The Python interval oracle independently compresses and expands full labels;
the native checker compares every interval endpoint on every tested ray step.
Graph budgets refuse; finite fit refusals are not counterexamples to BH.

Local compiler: Mojo 1.1.0.dev2026090805 (34562fa1), matching the repository
lock, with its existing minimal runtime paths configured locally. This is
not a claim of a full Pixi install or completed hosted acceptance. The new
workflow reruns under locked Pixi and regenerates every graph export.
No infinite-family boundary-hitting, G1 or PSC claim is promoted.
