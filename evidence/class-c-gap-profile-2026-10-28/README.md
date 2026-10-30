# Class-C gap profile (finite, exact)

Finite observations behind
[`docs/class-c-gap-uniformity-stopgo-2026-10-28.md`](../../docs/class-c-gap-uniformity-stopgo-2026-10-28.md).
Every graph is the complete canonical swap-seed overlap graph of
`(n+d, n, n−d+eps)` under the 20,000-state cap, built by
`kernel/class_c_gap_profile.mojo` (canonical). A capped graph or a vertex
without an offset-zero descendant aborts the run. Nothing here is uniform in
`n` or `d`.

| File | Command (from `kernel/`) | Content |
| --- | --- | --- |
| `frozen-tail-plus.txt` | `same 1 5 30 1 0 24` | gaps 5..30, `n = 4d..4d+24`: 650 members, one label set (196 labels, 77 typed rows), printed in full |
| `frozen-tail-minus.txt` | `same -1 5 30 1 4 28` | gaps 5..30, `n = 4d+4..4d+28`: 650 members, one label set (214 labels, 81 typed rows), printed in full |
| `middle-band-plus.txt` | `same 1 20 30 5 -16 -10` | gaps 20, 25, 30, `n = 4d−16..4d−10`: 21 members, one label set (280 labels, 139 typed rows) |
| `diagonals-plus.txt`, `diagonals-minus.txt` | `diagonals ±1 5 30 16` | vertex count at `n = 4d − j`, `j = −4..16` (rows), gaps 5..30 (columns); `.` is a screened non-PIP member |
| `native-test.log` | `tests/test_class_c_gap_profile.mojo` | regression receipt: frozen tails across gaps 6/9/12, below-onset negative controls, domain starts, refusals |

A typed row is `R top bottom s y k_lo k_hi` with `s = k + c + y`: the labels
`(top, bottom, k, c, y)` for `k_lo ≤ k ≤ k_hi` (the class-A dataset format).

## Replay

```
cd kernel
pixi run --locked mojo build -I . class_c_gap_profile.mojo -o /tmp/ccp
/tmp/ccp same 1 5 30 1 0 24     | cmp - ../evidence/class-c-gap-profile-2026-10-28/frozen-tail-plus.txt
/tmp/ccp same -1 5 30 1 4 28    | cmp - ../evidence/class-c-gap-profile-2026-10-28/frozen-tail-minus.txt
/tmp/ccp same 1 20 30 5 -16 -10 | cmp - ../evidence/class-c-gap-profile-2026-10-28/middle-band-plus.txt
/tmp/ccp diagonals 1 5 30 16    | cmp - ../evidence/class-c-gap-profile-2026-10-28/diagonals-plus.txt
/tmp/ccp diagonals -1 5 30 16   | cmp - ../evidence/class-c-gap-profile-2026-10-28/diagonals-minus.txt
pixi run --locked mojo run -I . tests/test_class_c_gap_profile.mojo
```

Each tail run takes about 20–30 minutes; the diagonal runs are dominated by
the near-edge members (thousands of vertices at large `d`).

Local compiler: Mojo 1.1.0.dev2026090805 (34562fa1), the lock pin, from
Modular's nightly wheels in a virtual environment rather than via Pixi.
