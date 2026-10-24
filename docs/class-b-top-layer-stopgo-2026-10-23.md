# Class B's top layer: stop/go for a residue-ray certificate (2026-10-23)

**Status:** stop/go note with an exact, bounded, exploratory profile. No
theorem, ledger node or claim status changes. This is lateral move 2 of the
[lateral-generalization strategy](lateral-generalization-strategy-2026-10-23.md),
restricted to the part of move 2 that no open PR covers. The class-A gaps
`d ≥ 5` are proved for `n ≥ 5d` by merged #335
([class-A gap theorem](class-a-gap-theorem-2026-10-23.md)); #334's sign
certificates are still open, and class C gaps `d ≥ 6` remain.

## Proposed target

Theorem C ([symbolic-cone note](p1b-symbolic-cone-2026-10-08.md)) proves BH,
PDS and G1 on class B below slope 5/2. Its §5 leaves open the **top layer**:

```text
plus   r = q + 1,  max(2q + 13, (5q + 10)/2) < p < 3q + 12,
minus  r = q − 1,  max(2q + 7,  (5q − 5)/2)  < p < 3q.
```

Put `g = 3q + 12 − p` (plus) or `g = 3q − p` (minus). So `g ≥ 1` is the
distance to the PIP boundary, and the probe's `d` is `g − 1`. For fixed `g`
the top layer is one line in `q`. For large `q` the window is
`1 ≤ g < (q + 14)/2` (plus) or `g < (q + 5)/2` (minus). It is therefore a
two-parameter family `(q, g)` with `g ≲ q/2`, the same shape as class A's
`(n, d)` gap family.

**Proposed claim.** For each branch, every gap `g ≥ 1` and every PIP member,
every vertex of the complete canonical swap-seed graph has an offset-zero
descendant. The certificate would be organized as residue rays `q = g l + r`,
as for class A. Theorem C then extends to all of class B, and with Corollary E2
and Proposition Z this gives PDS on all of class B.

## Prior art and transfer

The [class-A gap stop/go](class-a-gap-uniformity-stopgo-2026-10-23.md) table
applies unchanged:

- **Berthé–Bourdon–Jolivet–Siegel.** Its discrete planes need unimodularity,
  and class B has `|det M| = 2`.
- **Minervino–Thuswaldner.** It gives the non-unit representation space but no
  family result.
- **Akiyama–Gähler–Lee.** It needs trace ≤ 2, but class B has trace
  `r + 3 ≥ 3`.

Two more checks are specific to class B:

- **Barge's theorem.** Class B is constant on final letters (`x`) but not
  injective on initial letters (`x, c, c`), so it is outside Barge's class. The
  mode `barge 11 40` finds **0** Barge power/rotation witnesses (up to power 3)
  among all **708** PIP top-layer members with `g ≤ 12`, `q ≤ 40`.
- **The Theorem C note's own diagnosis.** Its §5 says the top layer "needs
  vertex families indexed by an extra variable and an inductive hitting
  argument". The probe below identifies that variable as the residue of `q`
  modulo the boundary gap `g`.

No source states a coincidence or PDS theorem for this family. Any novelty
lies in the certificate.

## Exact profile

`kernel/class_b_top_layer_profile.mojo BRANCH D QMAX` builds the complete
uncapped seed graph of every PIP member on one line and tests, for each modulus
`k ≤ 6`, whether the vertex counts on every residue class mod `k` are affine
over the last three points of that class. It raises on a capped graph or on any
vertex without an offset-zero descendant. Packet:
[`evidence/class-b-top-layer-profile-2026-10-23/`](../evidence/class-b-top-layer-profile-2026-10-23/).

| Branch | `g` | PIP members | Fit modulus | Increment per period | Fit window starts | Max first-hit depth |
| --- | --- | --- | --- | --- | --- | --- |
| plus | 1 | 24 (`q ≤ 26`) | 1 | +112 | q 24 (mod 1), q 9–15 (mod 6) | 7 → 19, about `q/2 + 6` |
| plus | 2 | 15 (`q ≤ 18`) | 2 | +112 | q 13–14 | ≤ 9 |
| plus | 3 | 26 (`q ≤ 30`) | 3 | +112 | q 22–24 | ≤ 10 |
| plus | 4 | 25 (`q ≤ 30`) | 4 | +112 | q 19–22 | ≤ 8 |
| plus | 5 | 24 (`q ≤ 30`) | 5 | +112 | q 16–20 | ≤ 7 |
| minus | 1 | 22 (`q ≤ 30`) | 1 | +112 | q 28 (mod 1), q 16–20 (mod 5) | 21 at `q = 30` |
| minus | 2 | 21 (`q ≤ 30`) | 2 | +112 | q 25–26 | 12 at `q = 30` |
| minus | 3 | 20 (`q ≤ 30`) | 3 | +112 | q 22–24 | 9 at `q = 30` |

What the profile shows:

1. **BH.** Every vertex of every graph has an offset-zero descendant.
2. **Period.** On every line the counts are periodic-affine in `q` with period
   exactly `g`. Where tested, the fits modulo multiples of `g` agree.
3. **Increment.** The increment is **112 vertices per period** on every line and
   both branches.
4. **Depth.** The first-hit depth is not bounded independently of the
   parameter: on `g = 1` it grows like `q/2`. A certificate therefore needs a
   parameter-dependent rank, as for class A slope one
   ([run-index note](p1b-class-a-run-index-2026-10-21.md)).
5. **Fit floors** grow with `g`, and the minus branch settles later than plus. At
   `q ≤ 18` plus `g = 3` fitted residues 0 and 2 but not 1 (differences 120, 120,
   112); at `q ≤ 30` all three fit. Both logs are kept as a reminder that a short
   window can miss a late floor.

**Caveat on the fit.** A three-point check is weak, and all of this is finite
evidence. It is the same kind of evidence that motivated class A's residue
rays, and there the real certificate was proved independently and refused
below its floors.

## Decision

**Proceed, narrowed**, in this order:

1. **Per-gap residue-ray certificates** for `g = 1, …, 5` on both branches. Use
   class A's ray machinery: carriers as typed run-index intervals affine in `l`
   with `q = g l + r`, the Perron signs in `A + qB` form, the child-index
   rounding `[⌈·/g⌉, ⌊·/g⌋]`, and an integer rank descent. Prove every finite
   prefix as an exact graph.
2. **A g-uniform regime certificate** that reuses the engine of merged #335 (with #334's sign certificates if they land)
   (`poly_hu` and Lemmas 1–4) once that lands. The stable increment of 112 per
   period across `g` is the signal that one regime table may serve every gap.

**Stop condition.** Stop if step 1 fails: the label sets are not affine in `l`
on some ray, or the rank fit fails the infinite-ray inequalities. Record the
failure as a negative control.

## Step 1 result (2026-10-24): label sets are affine, in the right basis

**The class-A encoding fails.** Class A's datasets group labels as k-intervals
at fixed `(top, bottom, k + c + y, y)`. On plus `g = 1` this finds **no** affine
floor up to `q = 26`. The cause is that every raw offset coordinate grows with
`q`: on that line `k`, `c` and `y` span about `±(q + 6)`, `±(3q + 18)` and
`±(6q + 34)`.

**The class-B basis.** A search over small integer functionals finds a rank-2
bounded lattice spanned by:

- `u = 3k + c + y`, with values in `[−4, 4]`;
- `v = 3k − c`, with values in `[−6, 6]`.

Their common kernel is the growth direction `(1, 3, −6)`. The map
`(k, c, y) → (u, v, k)` is unimodular, so k-intervals at fixed
`(top, bottom, u, v)` are a lossless encoding. This is class A's carrier shape
in class B's own coordinates.

**Results.** With that encoding, `labels BRANCH D QMAX` finds the following.
The fit holds over *all* members of each residue class past the floor.

| Line | Residue floors (`q mod g`) | Typed rows |
| --- | --- | --- |
| plus `g = 1` | 9 | 389 |
| plus `g = 2` | 12, 11 | 303, 297 |
| plus `g = 3` | 12, 16, 14 | 263, 287, 273 |
| plus `g = 4` | 16, 17, 18, 15 | 265, 247, 251, 271 |
| minus `g = 1` | 15 | 417 |
| minus `g = 2` | 18, 17 | 228, 218 |

Every endpoint slope seen on plus `g = 1` lies in `{−1, 0, 1}`. The windows
above the floors are short for `g = 3, 4`, as few as three or four members per
class. The packet is
[`evidence/class-b-top-layer-labels-2026-10-24/`](../evidence/class-b-top-layer-labels-2026-10-24/),
and it includes the failed class-A encoding as a negative control.

**Decision.** The step-1 stop condition is not met, so the route continues.
Step 2 is to port the ray certificate (carrier closure, then rank descent) to
class B. The new pieces it needs are:

- the `(u, v, k)` coordinates;
- class B's Perron polynomial and tile lengths;
- the child-index rounding by `g`.

## Non-claims

No class-B top-layer member is certified by this note. The profile is not a
certificate. The vertex-count fits do not imply the label sets are affine in
`l`; that is the step-1 check. Universal BH, A1′, #84, G1 and PSC remain open.
