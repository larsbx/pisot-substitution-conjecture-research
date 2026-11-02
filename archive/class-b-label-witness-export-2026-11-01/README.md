# Original Class-B witness exporter

`class_b_label_rays.mojo` is byte-for-byte the file at commit
`7c2d83fc8aa44db36662811d914ec146a161d269`, path
`kernel/class_b_label_rays.mojo`. Its SHA-256 is
`7b42520141e1c68de19f86880ebef1b2b61b3d521f5878798ba2207b2de33747`,
already pinned by the immutable packet's `inputs.json`.

The later optimization in `669e4630805f43c24b1506f1755dcf8f59baa64d`
replaced occurrence-order graph construction with segment-order construction.
Sorted vertices and first-hit depths are stable, but graph visitation and
the selected first shortest child need not be. The historical witness rows
encode those choices and their order. Reproduce their bytes with this
original exporter, compiled against the current locked dependency tree;
byte equality is still required, not assumed from the source pin.

This is an archived serialization replay, not a second live graph kernel.
The current native exporter still regenerates every sorted label export,
and its fresh witness output must independently pass complete coverage,
actual indexed letters, integer incidence/prefix shifts and depth descent.
The original witness output passes those same independent checks.

See `oracles/python/class_b_label_replay_compat.py` and
`evidence/class-b-witness-replay-reconciliation-2026-11-01/README.md`.
