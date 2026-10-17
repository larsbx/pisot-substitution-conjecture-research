# Class-D nearest-boundary calibration, 2026-10-14

Actual local Python-oracle replay only. The canonical Mojo companion is
unexecuted locally (Mojo/pixi absent); no canonical or universal claim is
credited by this packet. The existing all-seed graph oracle uses rational
field arithmetic and shortest reverse-graph target distances, without RNG.

Replay from repository root:

```sh
python3 oracles/python/class_d_boundary_probe.py
python3 -m pytest tests/test_class_d_boundary_probe.py
# With the locked canonical toolchain:
cd kernel && mojo run -I . class_d_boundary_probe.mojo
```

Deterministic finite domain: s=+/-1, a=0..3, b=0; eight graphs;
20,000-vertex cap per graph. The parameter wrapper refuses a outside 0..8.
A capped graph raises before producing depths. The recorded run completed
all eight uncapped graphs, with no target-free vertex. This is not family
exhaustion or a saturation test. The increasing-family proof remains open.

Observed sizes: plus 1026,977,887,868 (depth 6); minus 148,145,145,145
(depth 4). A plateau on three checked members does not certify a constant
graph or depth. Baseline dependencies are pinned by repository commit
83bdba801e8280cb0c9f440c83a0852319474767; source-digests.json additionally
pins the exact wrapper, oracle, canonical companion and regression bytes.
No time-based performance claim is made. source digests authenticate the
inputs; SHA256SUMS authenticates the files in this packet.
