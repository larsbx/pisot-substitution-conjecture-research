# Seam ceiling and endpoint functional — local acceptance, 18 November 2026

Base: `main@9dffd8a` (merge of #603). The
[note](../../docs/c4-neutral-rank-seam-ceiling-2026-11-18.md) carries the
mathematical contract and every non-claim. Runtime:
`Mojo 1.1.0.dev2026090805 (34562fa1)` from `kernel/pixi.lock`
(sha256 `1515f7300f49ad6b5e263a9bc02a8ec041123ce455b28fd24c440022824b2ff8`).
Hosted CI has not run. This packet claims no full Mojo-suite, Lean or Quint
run.

| Command (from `kernel/`) | Exit | Log |
| --- | --- | --- |
| `pixi run --locked mojo run -I . -I tests tests/test_seam_correction_ceiling.mojo` | 0 | [seam-ceiling.log](seam-ceiling.log) |
| `pixi run --locked mojo run -I . -I tests tests/test_promoted_endpoint_functional.mojo` | 0 | [promoted-endpoint.log](promoted-endpoint.log) |
| `pixi run --locked mojo run -I . -I tests tests/test_one_track_seam_spectrum.mojo` (existing) | 0 | [one-track-seam.log](one-track-seam.log) |
| `pixi run --locked mojo run -I . seam_ceiling_census.mojo` | 0 | [census.log](census.log) |

Source digests (sha256):

| File | Digest |
| --- | --- |
| `kernel/psc/seam_correction_ceiling.mojo` | `7e9e9e17c063ea1c80b5bb91675e4ff686228fd5707eb58d553c61afffe61d1c` |
| `kernel/psc/promoted_endpoint_functional.mojo` | `e2fb8b5c71d4fc723a98d0212889552026341a9484b9b42044a45bac34bc6318` |
| `kernel/tests/test_seam_correction_ceiling.mojo` | `464be46ca78b5d11473a46bce5736e68c1bf800573c00fc05775f3570345c04c` |
| `kernel/tests/test_promoted_endpoint_functional.mojo` | `51a294f9c0d93133f22637424f17c8a94ed9d6d80429c09b3db34b42ba71b3ca` |
| `kernel/seam_ceiling_census.mojo` | `2594d1640d8a26ac6600e24e4c6f94e6c17744449f9219881e087ff7fa691bdc` |

## Lean

`(cd proof/PscVerif && lake build PscVerif.NeutralRankSeam)` finished with
exit 0 and no warnings, using the pinned toolchain
`leanprover/lean4:v4.34.0-rc2` and the Mathlib cache from `lake exe cache get`.
`#print axioms` on `promoted_comp`, `promoted_adj`, `promoted_swap`,
`EndpointData.column_identity`, `vecMul_occ_eq`, `endpoint_rank_bound`,
`naive_fails`, `seam_det`, `seam_isInteriorAddress_1`, `_4`,
`seam_bigram_legal` and `seam_trace` reports only `propext`,
`Classical.choice` and `Quot.sound` (`seam_bigram_legal` does not need
`Classical.choice`). A full `lake build` of the library root with the new
import also exits 0. The isolated `tools/check_lean.sh` was not run.

## Cross-check against draft #602

[pr602-literal-01-122-201.log](pr602-literal-01-122-201.log) comes from a
checkout of the #602 head `cbb8c6c64b56bcce60c2e6031da7acb9ffc5b41d`. That
code is not on `main`. The driver below was run with the same lock:

```mojo
from psc.literal_seam_replay import literal_one_track_returns

def main() raises:
    var sigma: List[List[Int]] = [[0, 1], [1, 2, 2], [2, 0, 1]]
    for n in range(1, 13):
        try:
            var inv = literal_one_track_returns(sigma, n)
            var c = inv.fixed_counts()
            print(n, "first", c[0], "last", c[1], "seam", c[2], "U-L-R", c[2] - c[0] - c[1], "interior", len(inv.interiors))
        except e:
            print(n, "refused:", e)
```

Seam, last and first fixed counts are `24, 8, 12` at `n = 4, 8` and zero at
the other `n <= 11`. Power 12 refuses at the 100,000-letter word cap.

## Scratch only (not committed)

- A Python oracle for the endpoint-functional telescoping reproduced the
  Mojo counts on all six boxes: 0 failures, and naive failures
  42/38/22/16/20/40.
- #601's full-box scanner was run on the 252 unit members with a positive
  ceiling at order 1 or 2. The literal `(b1, b2)` equalled the whole-copy
  value every time. That run is not part of the committed census.
