# Class C, gaps d ≥ 6, below the onset: stop/go for the strip (2026-10-29)

**Status:** stop/go and design note with exact finite evidence; no theorem.
No claim status changes. Theorem T_C
([class-c-tail-theorem-2026-10-28.md](class-c-tail-theorem-2026-10-28.md))
proves boundary hitting (BH) on the frozen tail `n ≥ 4d` (plus) and
`n ≥ 4d + 4` (minus) for every gap `d ≥ 6`. This note takes the strip below
the onset, which T_C's non-claims redirected to a separate stop/go. The
strip runs down to the observed PIP domain start `n = 2d − 5` (plus) or
`2d + 1` (minus).

**Concurrent work.** PR #397 ([class-c-lower-strip-2026-10-29.md](class-c-lower-strip-2026-10-29.md)),
developed in parallel and merged first, proves the exact PIP domain (so the
domain starts above are proved, not just observed). It also certifies the
four diagonals nearest the onset, the middle cone at offsets 16, and the
gap-6 strip. The decision below is unchanged. T_C2 covers the whole band
`3d ≤ n` below the onset, including what #397 leaves open.

## Prior art

Same lines and mechanism as T_C, so the literature check of
[class-c-gap-uniformity-stopgo-2026-10-28.md](class-c-gap-uniformity-stopgo-2026-10-28.md)
transfers unchanged. `|det M| = 2` (non-unimodular), and no source proves pure
discrete spectrum for these two-parameter non-unimodular families. The method
is the repository's own two-parameter cone engine (`psc.symbolic_cone`,
[p1b-symbolic-cone-2026-10-08.md](p1b-symbolic-cone-2026-10-08.md)), whose
prior art is recorded there. Novelty would lie only in the certificate.

## Coordinates

Below the onset, write `k = n − 3d` and `j = 4d − n`, so that `d = k + j` and
`n = 4k + 3j`. The map `(d, n) ↔ (k, j)` is unimodular, so every lattice
point of the strip is an integer point `(k, j)`. In these coordinates the
run lengths are affine:

```text
(n + d, n, n − d + eps) = (5k + 4j, 4k + 3j, 3k + 2j + eps).
```

The onset is `j = 0` (plus) or `j = −4` (minus), and `k = 0` is the ray `n = 3d`.

## Exact finite evidence

Packet: [`evidence/class-c-strip-stopgo-2026-10-29/`](../evidence/class-c-strip-stopgo-2026-10-29/README.md).

**Columns.** Complete swap-seed graphs for every `n` from the domain edge to
the onset at `d = 16` and `d = 20`, both signs, give vertex counts by `k`:

| region (plus) | `d = 16` | `d = 20` |
| --- | --- | --- |
| `j = 1..9` (just below the onset) | 282, 282, 276, 278, 196, 180, 228, 204, 198 (by `j` = 9..1) | identical |
| middle, `0 ≤ k` and `j ≥ 10` | 280 throughout | 280 throughout |
| `k = −1..−10` | 282, 321, 316, 333, 368, 379, 394, 478, 420, 438 | identical |
| edge, `n = 2d − 5` (first PIP member) | 3734 | 4214 |

Minus is the same picture: the middle band (`k ≥ 6`, `j ≥ 4`) has 250 vertices
and the edge (`n = 2d + 1`) has 2559 → 3039 vertices. The finite profile of
#374 (`diagonals-*.txt`, gaps 5–30) shows the same: each diagonal of fixed
`j` and each line of fixed `k` freezes in `d` past a floor, while the
vertex count at a fixed distance from the domain edge grows by about 120 per
gap.

**Diagonals.** The canonical piece certificate of T_C
(`class_c_tail_certificate.mojo piece`, a diagonal `n = 4d − j` for all
`d ≥ d0`) certifies every diagonal `j = 1..12` on both signs. Every vertex
hits, offsets are constant, and the first certifying floors are recorded in
`diagonal-floors.txt`. From `j = 6` on, the first floor is exactly where
`k = n − 3d` reaches 3 (plus) or 8 (minus).

**Middle sector (prototype).** A scratch driver on the unchanged cone engine
treats the sector `k ≥ k0`, `j ≥ j0` as one two-parameter cone. It certifies
PIP, every vertex hitting and constant offsets:

| sign | sector | vertices | refused at |
| --- | --- | --- | --- |
| plus | `k ≥ 4`, `j ≥ 14` | 280 | `k ≥ 0, j ≥ 10` and `k ≥ 2, j ≥ 12` (a sign at beta undecided) |
| minus | `k ≥ 8`, `j ≥ 6` | 250 | `k ≥ 6, j ≥ 4` (same) |

## Proposed claim

**Target (Theorem T_C2).** For each sign, every class-C member with
`3d ≤ n` below the onset (`n < 4d` plus, `n < 4d + 4` minus) is PIP, and every
vertex of its complete swap-seed overlap graph has an offset-zero
descendant. This holds for every gap `d`; there is no gap floor, because the
`(k, j)` orthant contains every gap and its small corner is decided exactly.

The proof shape is T_C's cover, with the frame changed from `(d, n − 4d)` to
`(k, j)`:
- the middle sector at a certifying shift;
- the edge lines of fixed `k` and the diagonals of fixed `j` it leaves, each
  a one-parameter piece;
- the finitely many members below the lines' floors, decided by the exact kernel.

Unlike T_C, the pieces carry different label sets (196 to 282 vertices). BH
needs only hitting, PIP and the exact cross-check per piece, so the cover
records the sets instead of requiring one.

With T_C, this would leave class C's BH residual for `d ≥ 6` as the
**lower cone** `2d − 5 ≤ n < 3d` (plus) and `2d + 1 ≤ n < 3d` (minus).

## Decision

- **Go** for T_C2 on both signs. Extend `psc.class_c_tail_certificate` to
  pieces in the `(k, j)` frame and to covers with several label sets; keep T_C's
  pieces, names and logs byte-identical.
- **Redirect** the lower cone. Lines of fixed `k < 0` do freeze (`k = −1..−10`
  agree at `d = 16, 20`), but the graphs near the domain edge grow with `d`.
  No single finite graph covers that region, so it needs a carrier-type
  argument with labels affine in a parameter, as in class B's Theorems A_B/B_B.
  It gets its own stop/go after T_C2.

## Non-claims

- Nothing here is uniform: the columns are two gaps, the diagonals 12 per
  sign, and the sector results come from a scratch driver.
- The PIP domain start and the edge growth rate are observations.
- No BH, G1 or PSC claim changes.
