# Class C below the onset: Theorem T_C2, the band 3d ≤ n (2026-10-29)

**Status:** repository-proved, computer-assisted, at the stated scope. Local
native validation is complete; hosted acceptance and independent human review
are pending. Design and evidence for the go decision:
[class-c-strip-stopgo-2026-10-29.md](class-c-strip-stopgo-2026-10-29.md).
Canonical code: `kernel/psc/class_c_tail_certificate.mojo` (the `STRIP`
frame) and the driver `kernel/class_c_tail_certificate.mojo strip`. Packet:
[`evidence/class-c-strip-theorem-2026-10-29/`](../evidence/class-c-strip-theorem-2026-10-29/README.md).

## Statement

For the class-C lines `sigma(x) = x y^(n+d) x`, `sigma(c) = c y^n x`,
`sigma(y) = c y^(n-d+eps) c`, `eps = ±1`:

**Theorem T_C2 (scoped, computer-assisted).** Let `d ≥ 1` and `3d ≤ n`, with
`n < 4d` (`eps = +1`) or `n < 4d + 4` (`eps = −1`). Then the member is PIP, and
every vertex of its complete canonical swap-seed overlap graph has an
offset-zero descendant.

On this band the label set is **not** one set. Plus has 25 distinct sets and
minus has 49, with 180 to 346 vertices on the symbolic pieces. For large
`d`, the middle sector carries one set (280 labels plus, 250 minus).

**With T_C.** [Theorem T_C](class-c-tail-theorem-2026-10-28.md) proves BH on
`n ≥ 4d` (plus) and `n ≥ 4d + 4` (minus) for every `d ≥ 6`, so for every gap
`d ≥ 6`, BH now holds on `n ≥ 3d`. Class C's open BH residual for `d ≥ 6`
narrows to the **lower cone** `2d − 5 ≤ n < 3d` (plus) and `2d + 1 ≤ n < 3d`
(minus). Those lower ends are now proved, not observed: they are the exact
PIP domain of the domain lemma in
[class-c-lower-strip-2026-10-29.md](class-c-lower-strip-2026-10-29.md) (#397). For `d ≤ 5`, T_C2
re-proves part of what the gap-4 and gap-5 line certificates already cover.

**Relation to #397.** #397 was developed concurrently and merged first. Its
certificates are:
- the four diagonals nearest the onset, for every `d ≥ 6`;
- the middle cone `3d + 16 ≤ n ≤ 4d − 16` (`d ≥ 32`), with the same 280/250 sets;
- the gap-6 strip, exactly.

After #397 it records open bands `3d ≤ n ≤ 3d + 15` and `4d − 15 ≤ n ≤ 4d − 5`
(plus; `4d − 1` minus) for `d ≥ 32`, and the whole upper strip for
`7 ≤ d ≤ 31` apart from those diagonals. T_C2 covers all of them, and
overlaps #397's pieces without depending on them. The two results agree
wherever both apply: the same middle-sector sets, and the same diagonal
vertex counts (180, 228, 204, 198 plus; 212, 238, 222, 216 minus).

## Proof

**Frame.** Put `k = n − 3d` and `j = 4d − n`. Then `d = k + j`, `n = 4k + 3j`,
and the change of coordinates is unimodular. The band is
`{k ≥ 0, j ≥ 1}` (plus) and `{k ≥ 0, j ≥ −3, k + j ≥ 1}` (minus). The run lengths
`(n + d, n, n − d + eps) = (5k + 4j, 4k + 3j, 3k + 2j + eps)` are affine. A
`Piece` in the `STRIP` frame is a cone, a diagonal (`j` fixed) or a line (`k`
fixed) in these coordinates. Everything else is T_C's machinery, unchanged:
- the class-C cone with its bracket proposals;
- `certify_cone`'s PIP proof and the closure, sound by Lemma S′ of
  [p1b-symbolic-cone-2026-10-08.md](p1b-symbolic-cone-2026-10-08.md);
- per piece: every vertex reaches offset zero, offsets are constant, and the
  graph is cross-checked against the exact graph at one member (not part of
  the proof).

**Cover.** The diagonals just below the onset carry their own label sets, so
they come first:
- plus, `j = 1..13`, each for `k ≥ 0`;
- minus, `j = −3..5`, each for `k ≥ max(0, 1 − j)`.

Each is covered by T_C's line rule: certified from its first certifying
shift, with the members below decided by the exact kernel. Then the middle
sector `k ≥ 0, j ≥ 14` (plus) or `j ≥ 6` (minus) is covered by T_C's cone rule.
The cone is certified at the first certifying shift, and its edge strips are
lines. Only an undecided sign or fit leads to a shift. Any other failure
aborts the cover: PIP failure, a vertex that doesn't reach offset zero, a
non-constant offset, a failed cross-check, or a screened member. The run:

| sign | middle cone | its edge lines | diagonals | exact members |
| --- | --- | --- | --- | --- |
| plus | `k ≥ 3, j ≥ 17` (280) | `k = 0, 1, 2` (`j ≥ 14`); `j = 14, 15, 16` (`k ≥ 3`) | `j = 1..13`, from `k ≥ 2..6` | 45 |
| minus | `k ≥ 8, j ≥ 14` (250) | `k = 0..7` (`j ≥ 6` or `8`); `j = 6..13` (`k ≥ 8`) | `j = −3..5`, from `k ≥ 6..10` | 70 |

There are 20 symbolic pieces on plus and 26 on minus. Every exact member
below a floor, from `d = 1` up, is PIP; none was screened out. These
pieces and members exhaust the band by construction, as for T_C. An
independent count over `k, j < 80` from the logs finds no hole and no
overlap. `square`

**Why the shifts.** As for T_C, some intermediate decision (a run end
clipping a realness interval) changes sign close to the band's edges, though
the label set of each piece is fixed. The shift-0 sector cones refuse on an
undecided sign at beta; their shifted cones certify.

## Evidence and replay

From `kernel/`:

```
mojo run -I . class_c_tail_certificate.mojo strip 1     # plus
mojo run -I . class_c_tail_certificate.mojo strip -1    # minus
mojo run -I . tests/test_class_c_strip_certificate.mojo
```

Each sign takes about 50 minutes locally, with both signs running at once on
4 cores. The logs list every piece tried, certified or undecided, and every
exact member, then the distinct label sets as typed rows. The workflow
`class-c-tail-theorem.yml` (job `strip`) replays both and diffs them against
the packet. The `STRIP` frame was added without changing T_C: T_C's two
theorem logs and its test receipt replay byte-identically after the change.

## Negative controls

- **Refusal, not decision.** The shift-0 middle cones refuse on an undecided
  sign at beta, so the cover shifts instead of treating the refusal as a verdict.
- **The stop/go's below-onset control** still stands. The diagonal `j = 1`
  (plus) certifies with 198 labels, a different set from T_C's 196.
- **Malformed strip pieces refuse** (tested): an offset `c ≠ 0`, a corner with
  `d < 1`, `|j0| > 64`, sign 0.
- **Several sets are recorded, not merged.** The several-set cover keeps
  distinct sets (tested); T_C's one-set cover still refuses a second set.

## What is trusted

The same as T_C: Lemma S′ and the engine `psc.symbolic_cone`, the exact
kernel for the members, and the driver code. That code is now the `STRIP`
frame's coefficient map `d = k + j`, `n = 4k + 3j` and the several-set cover.

## Non-claims / remaining gaps

- **The lower cone stays open** for every `d ≥ 7`: `2d − 5 ≤ n < 3d` (plus),
  `2d + 1 ≤ n < 3d` (minus). At `d = 6`, #397 decides it exactly. There the
  graphs near the domain edge grow with `d` (stop/go), so it needs a
  carrier-type argument with its own stop/go.
- **Only BH.** No pure-discrete-spectrum, G1 or PSC claim is made.
- **No claim status changes.** The completion ledger's obligation 1
  (class-C part) narrows to the lower cone.
- Independent human review is pending.
