# Class-B leftover-gap rays (2026-10-27)

Packet for [docs/class-b-gap-rays-2026-10-27.md](../../docs/class-b-gap-rays-2026-10-27.md):
62 residue rays on plus `g = 6..10` and minus `g = 4..7`.

| file | content |
| --- | --- |
| `labels/` | 627 exact native label sets (`kernel/class_b_label_rays.mojo BRANCH G Q`), the fitting input |
| `carriers.json` | fitted carriers (`class_b_gap_rays.py`); `certify_floor` where the certificate refused at the fitted floor |
| `fit.log` | refit from `labels/`; equals `carriers.json` except for `certify_floor` |
| `certify.log` | per ray index 0..82: native `certify`, `replay` at `q0` and `q0 + g`, `below` |
| `oracle.log` | `python oracles/python/class_b_ray_certificate.py` (all 83 rays) |
| `native.counts`, `oracle.counts` | the two count streams; identical |
| `provenance.log` | revision, runtime and commands |

Replay: see the note's *Evidence and replay*. `sha256sum -c SHA256SUMS` checks
every file here.
