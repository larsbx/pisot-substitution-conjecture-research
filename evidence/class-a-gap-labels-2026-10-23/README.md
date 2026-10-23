# Class-A gap label datasets and regime fits — 2026-10-23

Step (a) of `docs/class-a-gap-uniformity-stopgo-2026-10-23.md`. This packet is
a finite observation, not a certificate.

- `labels-dD-epsE.txt`: one file per line `(n+D, n, n+E)`, written by
  `kernel/class_a_gap_regimes.mojo build D E 5 9 <this dir> 4 16`. Each
  member `n = D l + r`, `5 <= l <= 9`, in the line's domain is the exact
  complete swap-seed graph (20,000-state cap, every vertex hitting, else the
  build aborts). It is stored as `M n vertices max_depth rows` followed by its
  maximal typed k-intervals `R top bottom s y k_lo k_hi`, in increasing `n`.
  - Complete: `D = 1..16`, both signs; `D = 17` plus.
  - `D = 17` minus: 80 of 85 members, from a build stopped at its time
    limit. Rerunning the same command resumes it.
- `build.log`: the `D_GAP_DATASET` lines of the build.
- `fits/fit-epsE-JJ.log` / `.exit`, `fits/table-epsE-JJ.txt`:
  `class_a_gap_regimes.mojo fit E <this dir> 5 16 J 5 <table>`. Each regime is
  fitted exactly over Q, or its first obstruction is named. Tables hold
  `T eps kind j j1 d_min rows`, then per row `F top bottom s y` followed by the
  integer coefficients of `k_lo` and `k_hi` over the basis `[n, l, d, 1]`
  (boundary regimes) or `[n, l, d, r, 1]` (middle). `kind` is 0 low, 1 high,
  2 middle.
- `gap-regimes-tests.log` / `.exit`: `kernel/tests/test_class_a_gap_regimes.mojo`.
- `mojo-version.txt`: the lock-matched compiler. This is not a CI receipt.

The files are byte-identical at any worker count; the test checks this at 1
and 4 workers.

```sh
(cd kernel && pixi run --locked mojo run -I . class_a_gap_regimes.mojo build 6 -1 5 9 /tmp/gap 4 16)
cmp /tmp/gap/labels-d6-eps-1.txt evidence/class-a-gap-labels-2026-10-23/labels-d6-eps-1.txt
(cd kernel && pixi run --locked mojo run -I . class_a_gap_regimes.mojo fit -1 ../evidence/class-a-gap-labels-2026-10-23 5 16 3 5 /tmp/t.txt)
(cd evidence/class-a-gap-labels-2026-10-23 && sha256sum -c SHA256SUMS)
```

`SHA256SUMS` covers every file in this packet except itself.
