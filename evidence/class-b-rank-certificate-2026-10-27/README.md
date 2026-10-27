# Class-B g=1 piecewise rank certificates (plus and minus)

`plus-g1-r0.cert` is the certificate (format in
`kernel/psc/class_b_rank_certificate.mojo`): a header `C plus 1 0 10`
(branch, gap, residue, floor q0), 1,787 rows
`P top bottom s d lo_slope lo0 hi_slope hi0 a b c target` (one integer potential
`X = a*q + b*k + c` per segment), and 2,302 rows
`E parent child dx lo_slope lo0 hi_slope hi0`, all ends affine in `t = q − q0`.

`minus-g1-r0.cert` is the transferred minus g=1 certificate in the same format
(header `C minus 1 0 16`, 1,301 pieces, 1,970 edges).

| File | Content |
| --- | --- |
| `check.log`, `minus-check.log` | native all-parameter checks |
| `replay.log`, `minus-replay.log` | native replays of (H1),(H2) on plus q=10..42, minus q=16..42 |
| `oracle.log`, `minus-oracle.log` | independent oracle: check, then the same replays |
| `native-test.log` | Mojo regression receipt (toy, six negative controls, both certificates, q=10 and q=16 replays) |
| `edge-exports.sha256` | digests of the 60 native `edges` exports replayed (not stored: 1.5–21 MB each) |
| `inputs.json` | digests of the sources used, compiler and solver versions |
| `SHA256SUMS` | this packet byte-for-byte |

Training windows: plus q=10..26 and minus q=16..30. The holdouts (plus 27..42,
minus 31..42) were not used by the synthesis. No boundary-hitting, G1 or PSC
claim is promoted: each rank is conditional on carrier inclusion and actual
symbolic edges for every q at or above its floor.

## Replay

From `kernel/` with the locked environment:

```
pixi run --locked mojo run -I . tests/test_class_b_rank_certificate.mojo
pixi run --locked mojo build -I . class_b_rank_certificate.mojo -o /tmp/rank-cert
pixi run --locked mojo build -I . class_b_label_rays.mojo -o /tmp/class-b-label-rays
/tmp/rank-cert check ../evidence/class-b-rank-certificate-2026-10-27/plus-g1-r0.cert
for q in $(seq 10 42); do /tmp/class-b-label-rays plus 1 $q edges > /tmp/edges/plus-g1-q$q.edges; done
for q in $(seq 10 42); do /tmp/rank-cert replay ../evidence/class-b-rank-certificate-2026-10-27/plus-g1-r0.cert /tmp/edges/plus-g1-q$q.edges; done
/tmp/rank-cert check ../evidence/class-b-rank-certificate-2026-10-27/minus-g1-r0.cert
for q in $(seq 16 42); do /tmp/class-b-label-rays minus 1 $q edges > /tmp/edges/minus-g1-q$q.edges; done
for q in $(seq 16 42); do /tmp/rank-cert replay ../evidence/class-b-rank-certificate-2026-10-27/minus-g1-r0.cert /tmp/edges/minus-g1-q$q.edges; done
```

From the repository root:

```
python oracles/python/class_b_rank_certificate_oracle.py evidence/class-b-rank-certificate-2026-10-27/plus-g1-r0.cert /tmp/edges/plus-g1-q{10..42}.edges
python -m pytest -q tests/test_class_b_rank_certificate.py
python oracles/python/class_b_rank_certificate_oracle.py evidence/class-b-rank-certificate-2026-10-27/minus-g1-r0.cert /tmp/edges/minus-g1-q{16..42}.edges
# optional, needs scipy; regenerates both certificates byte-for-byte here:
python oracles/python/class_b_rank_synthesis.py /tmp/edges plus 1 10 26 /tmp/plus-g1-r0.cert
python oracles/python/class_b_rank_synthesis.py /tmp/edges minus 1 16 30 /tmp/minus-g1-r0.cert
```

Each export takes about 20–100 s; the full q=10..42 export is about 35 minutes
serially. CI regenerates plus q=10, 26, 27, 42 and minus q=16, 30, 31, 42 and compares digests.

Local compiler: Mojo 1.1.0.dev2026090805 (34562fa1), the lock pin, installed
from Modular's nightly wheel index into a virtual environment rather than via
Pixi. Synthesis: scipy 1.18.1 (HiGHS). This is not a claim of a hosted Pixi run.
