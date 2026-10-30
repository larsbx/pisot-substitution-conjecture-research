# Class-C strip below the onset: finite evidence for the stop/go

Receipts for [`docs/class-c-strip-stopgo-2026-10-29.md`](../../docs/class-c-strip-stopgo-2026-10-29.md).
Every number comes from canonical Mojo code. Nothing here is uniform in `n` or `d`.

| File | Command (from `kernel/`) | Content |
| --- | --- | --- |
| `column-d16_e1.txt`, `column-d20_e1.txt` | `class_c_gap_profile.mojo profile D 1 2D-6 4D+4` | `n` and vertex count of the complete graph (`S` = screened non-PIP) |
| `column-d16_e-1.txt`, `column-d20_e-1.txt` | `class_c_gap_profile.mojo profile D -1 2D-6 4D+4` | the same, minus |
| `diagonal-floors.txt` | `class_c_tail_certificate.mojo piece EPS C D0 0 diagonal` for `D0 = 6, 7, …` until it certifies | first certifying gap floor of the diagonal `n = 4d + C`, with `C = −j` (plus) or `4 − j` (minus), `j = 1..12`, and its vertex count |

The column files keep only `n` and the vertex count from each member block:

```
mojo run -I . class_c_gap_profile.mojo profile D EPS NMIN NMAX \
  | awk '/^[MS] /{print $2, ($1=="S"?"S":$3)}'
```

The `diagonal-floors.txt` lines were produced by a scratch loop around the
canonical `certify_piece`, at the merged revision `eff1bd37`. The loop
printed `diag` for the kind that the canonical driver calls `diagonal`. The
middle-sector results quoted in the note come from a scratch driver on the
unchanged `psc.symbolic_cone`. They are a prototype, not a receipt; T_C2 will
make them canonical.

Local compiler: Mojo 1.1.0.dev2026090805 (the lock pin), from Modular's
nightly wheels.
