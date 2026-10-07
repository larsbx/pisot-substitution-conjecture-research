# Unbounded `Z_2` route: exploratory drivers

**Status:** exploratory scratch, kept for reproducibility. Nothing here is
cited by a proof or a census, and these drivers have no regression tests.
The canonical code is `kernel/odd_letter_family_certificate.mojo`.
Side-notes ledger, 2026-10-07 ("the z_floor cover run") records what they
measured.

| File | What it runs |
| --- | --- |
| `onepat.mojo` | `cover_pattern_guided` on one run pattern, in z_floor mode, verbose: `onepat s delta floor budget l1 open1 l2 open2` (`l1`, `l2` like `zy`, `-` for empty, `open` 0/1) |
| `zruns.mojo` | every fully revealed pattern with `w_1` (or `u`) of at most `r1` runs and `w_2` of at most `r2`, every run length symbolic: `zruns s delta floor r1 r2 budget` |

Build from `kernel/`:

```sh
pixi run mojo build -I . ../experiments/z2-route/zruns.mojo -o /tmp/zruns
```
