# Class-B top-layer piecewise rank certificates (all 21 residue rays)

`certificates/<ray>.cert`, one per residue ray (`plus-g1-r0` … `plus-g5-r4`,
`minus-g1-r0` … `minus-g3-r2`), in the format of
`kernel/psc/class_b_rank_certificate.mojo`: a header `C branch gap residue q0`,
rows `P top bottom s d lo_slope lo0 hi_slope hi0 a b c target` (one integer
potential `X = a*q + b*k + c` per segment) and rows
`E parent child dx lo_slope lo0 hi_slope hi0`, all ends affine in
`t = (q − q0)/gap`.

| File | Content |
| --- | --- |
| `rays.json` | per ray: label-ray floor, rank floor and the refusal text for every skipped floor, training window, replayed members, holdout count, pieces, symbolic edges, segments, guided/completed, certificate edges, coefficient bounds |
| `logs/<ray>.check.log` | native all-parameter check |
| `logs/<ray>.replay.log` | native replay of (H1),(H2) on every member from the floor through q=48 |
| `logs/<ray>.oracle.log` | independent oracle: check, then the same replays |
| `native-test.log` | Mojo regression receipt (toy, six negative controls, all 21 checks, plus q=9 and minus q=16 replays) |
| `edge-exports.sha256` | digests of the 271 native `edges` exports replayed (not stored: up to 16 MB each) |
| `inputs.json` | digests of the sources used, compiler and solver versions |
| `SHA256SUMS` | this packet byte-for-byte |

Training windows end at q ≤ 30 (plus g=1: q ≤ 26); every later member is a
holdout, and members q=43..48 lie beyond the label-ray packet. No
boundary-hitting, G1 or PSC claim is promoted: each rank is conditional on
carrier inclusion and actual symbolic edges for every member at or above its
floor.

## Replay

From `kernel/` with the locked environment, for one ray (`B G R` its branch,
gap, residue; members `Q` from its floor in steps of `G` through 48):

```
pixi run --locked mojo run -I . tests/test_class_b_rank_certificate.mojo
pixi run --locked mojo build -I . class_b_rank_certificate.mojo -o /tmp/rank-cert
pixi run --locked mojo build -I . class_b_label_rays.mojo -o /tmp/class-b-label-rays
/tmp/rank-cert check ../evidence/class-b-rank-certificate-2026-10-27/certificates/B-gG-rR.cert
/tmp/class-b-label-rays B G Q edges > /tmp/edges/B-gG-qQ.edges
/tmp/rank-cert replay ../evidence/class-b-rank-certificate-2026-10-27/certificates/B-gG-rR.cert /tmp/edges/B-gG-qQ.edges
```

From the repository root:

```
python oracles/python/class_b_rank_certificate_oracle.py evidence/class-b-rank-certificate-2026-10-27/certificates/B-gG-rR.cert /tmp/edges/B-gG-q*.edges
python -m pytest -q tests/test_class_b_rank_certificate.py
# optional, needs scipy; regenerates the certificate byte-for-byte here
# (training window from rays.json):
python oracles/python/class_b_rank_synthesis.py /tmp/edges B G FLOOR TRAINING_LAST /tmp/B-gG-rR.cert
```

An export takes from a few seconds (g=5, small q) to a few minutes (g=1,
q=48). CI regenerates, per ray, the floor, the first holdout and the last
replayed member, compares their digests, and replays them under both checkers.

Local compiler: Mojo 1.1.0.dev2026090805 (34562fa1), the lock pin, installed
from Modular's nightly wheel index into a virtual environment rather than via
Pixi. Synthesis: scipy 1.18.1 (HiGHS). This is not a claim of a hosted Pixi run.
