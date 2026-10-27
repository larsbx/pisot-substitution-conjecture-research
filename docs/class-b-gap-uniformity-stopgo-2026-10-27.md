# Class B's top layer, step 2b: stop/go for a certificate uniform in the gap (2026-10-27)

**Status:** stop/go note with an exploratory finite profile; no theorem, no
certificate, no claim. Step 2 ([class-b-ray-certificate-2026-10-27.md](class-b-ray-certificate-2026-10-27.md))
certifies eight lines, plus `g ≤ 5` and minus `g ≤ 3`. What remains of class B's
top layer is one line per gap, plus `g ≥ 6` and minus `g ≥ 4`: an infinite
family that ray-by-ray tabulation cannot exhaust. This is step 2 of the
[top-layer stop/go](class-b-top-layer-stopgo-2026-10-23.md)'s decision list
("a g-uniform regime certificate").

## Proposed claim

For each branch `eps = ±1`, every gap `g ≥ g0` and every `q` in the open top
layer of the line `(p, q, r) = (3q + 6 + 6eps − g, q, q + eps)`, every vertex of
the complete canonical swap-seed overlap graph has an offset-zero descendant.
The proof would be **one** certificate per branch, quantified over `(l, g, r)`
with `q = g l + r`, organized in residue *regimes* as class A's
[d-uniform certificate](class-a-gap-uniform-certificate-design-2026-10-23.md)
is.

## Prior art and transfer

No new source search was needed. The question is the class-B analogue of
[class A's gap-uniformity stop/go](class-a-gap-uniformity-stopgo-2026-10-23.md),
and its table transfers unchanged. Berthé–Bourdon–Jolivet–Siegel prove pure
discrete spectrum for infinite families of products, but they need
unimodularity, and class B has `|det M| = 2`. Minervino–Thuswaldner give no
family result. Akiyama–Gähler–Lee need trace `≤ 2`, and class B's trace is
`r + 3 ≥ 3`. The [top-layer stop/go](class-b-top-layer-stopgo-2026-10-23.md)
also found 0 Barge-class witnesses among 708 PIP members. No source states a
family result for these lines. Novelty would lie in the certificate.

## What a g-uniform certificate must change: the carrier

**The reachable graph is not g-uniform.** Step 2's carriers are fits of the
exact reachable label sets. Across `g`, the fitted tables keep three slope
classes of `k`-endpoints with constant row counts on every ray: `(−1, 0)` with
35, `(−1, 1)` with 21 and `(0, 1)` with 35. The `(0, 0)` class does not keep
its count. It is a bounded core with `|u| ≤ 3`, `|k| ≤ 2`, `|d| ≤ 6`, whose
reachable part changes with `g`: 106, 80, 80, 80, 70, 74, 66, 53, 60 and 51 rows
at plus `g = 1..10`, the same for every residue of a gap. Which core labels are
*reachable* is not a function of a regime.

**A closed superset is enough.** Theorem A_B of step 2 uses only containment,
`G_q ⊆ C_q`. Take instead

```text
C_q = forward closure, under strict children, of the strict core
      { (t, b, w) strict : |u| ≤ 3, |d| ≤ 6, |k| ≤ 2 },  u = 3k+c+y, d = c−3k.
```

Its definition involves strictness only, in which `g` enters symbolically
through `L_x = 3β² + (3 + 3eps − g)β + 3eps` and the `−gβk` term of `T`.

**Observed (floating point, `oracles/python/class_b_core_closure.py`):**

| member | `|C_q|` | `|G_q|` (native) | `G_q ⊄ C_q` | `C_q` states reaching offset zero |
| --- | ---: | ---: | ---: | ---: |
| plus `g=1`, `q=20` | 5481 | 3997 | 0 | 5481 |
| plus `g=6`, `q=40` | 2523 | 1063 | 0 | 2523 |
| plus `g=8`, `q=40` | 2257 | 758 | 0 | 2257 |
| plus `g=10`, `q=40` | 2101 | 608 | 0 | 2101 |
| minus `g=3`, `q=30` | 2663 | 1276 | 0 | 2663 |

**Sweep.** All 839 native graphs exported for this note satisfy `G_q ⊆ C_q`,
and every state of each `C_q` reaches offset zero. They cover plus `g = 1..10`
(`q ≤ 42` for `g ≤ 5`, up to `q = 6g + 30` beyond) and minus `g = 1..8`
(`q ≤ 42` for `g ≤ 3`, up to `q = 69` for `g = 7`, and only `q ≤ 21` for
`g = 8`). The 1,818 core closures of the regime profile below were likewise
all closed without hitting the cap, and every state reached offset zero (the
generator refuses otherwise).

**The core stabilizes in `g`.** Strictness of a core label compares polynomials
in `β` whose coefficients are linear in `g`. As `β → ∞` the leading
coefficient decides, and where it vanishes, the sign of the `β` coefficient
changes at a threshold `g = −c1/c2`. Over the whole core, on both branches, the
largest such threshold is `g = 9`. For example, the type-`(x, x)` label at
`(u, d, k) = (−3, −5, 0)` on plus has `T = −3β² + 2β + 5` against
`L_x = 3β² + (6 − g)β + 3`, so it is strict iff `(g − 8)β < 8`. Past `g = 9`, the
core's strict pattern is constant in `g`, asymptotically in `β`.

**Negative control: all strict labels is too much.** The window strict set
`{|u| ≤ 5, |d| ≤ 8}` at plus `g = 10`, `q = 40` has 24,813 states. It is not
closed (401,570 strict children leave it), and only 19,713 of its states reach
offset zero inside it. The carrier must be a closure, not a strictness window.

## Regime profile

Core-closure carriers were generated for plus `g = 8..20` and minus
`g = 6..16`, every residue, `q = 4g .. 10g − 1` (1,818 members), and fitted ray
by ray exactly as in step 1: the earliest floor whose first two members
predict every later member. `oracles/python/class_b_regime_probe.py` then asks
whether the rays of one residue regime share **one** table, with constant
`l`-slopes and intercepts affine in `g` (low `r = j`, high `r = g − j`), or
affine in `(g, r)` (middle, `j0 ≤ r ≤ g − j1`). Rows are keyed by slice and
ordinal, since a slice `(t, b, u, d)` may hold several `k`-intervals. An
earlier keying by the slice alone silently dropped intervals; every number
below is from the corrected probe.

| branch | regime | one table from | rows |
| --- | --- | --- | ---: |
| plus | low `j = 0, …, 4` | `g = 14, 15, 16, 17, 18` | 541, 531, 529, 529, 529 |
| plus | high `j = 1, …, 16` | `g = 13, 12, 11, 10, 10, 10, 10, 11, 12, 12, 13, 14, 15, 16, 17, 18` | 529–603 |
| plus | **middle `2 ≤ r ≤ g − 14`** | `g = 16` (15 rays, `g = 16..20`) | 529 |
| minus | low `j = 0, …, 8` | `g = 10, 10, 10, 10, 10, 11, 12, 13, 14` | 529–571 |
| minus | high `j = 1, …, 8` | `g = 10, 10, 10, 10, 11, 12, 13, 14` | 529–551 |
| minus | **middle `6 ≤ r ≤ g − 6`** | `g = 12` (15 rays, `g = 12..16`) | 529 |

**Both branches are covered in the probed windows.**

- **Minus, `g ≥ 12`:** every residue lies in low `j ≤ 5`, middle `[6, g − 6]`
  or high `j ≤ 5`.
- **Plus, `g ≥ 16`:** every residue lies in low `j ≤ 1`, middle `[2, g − 14]` or
  high `j ≤ 13`.

This is class A's low/middle/high shape. The two middle tables have the same
529 slices, and their rows agree on 313 of them; they differ in intercepts.
Away from the anchor, plus's regimes settle to 529-row tables too (low
`j = 2..4`, high `j = 14..16`), which is the middle table seen from either
side.

**The anchored band.** The residue dependence concentrates around
`s = (q + 5) mod g ≡ 0` on plus, where `q + 5 ≈ β` (`β − q ∈ (4.8, 5.1)`). At
`g = 16`, consecutive residues differ by 3–9 rows at `r = 1..3` (`s = 6..8`) and
by 59–132 rows at `r = 5..10`. Regimes stabilize from the anchor outward: high
`j = 4..7` from `g = 10`, and about one more gap per step away from it. The band
is about 15 residues wide on plus (`r = g − 13 .. g + 1`, wrapping) and about 11
on minus, so the middle opens at `g = 16` and `g = 12` respectively.

**What is left over.** The gaps below the regime floors are finitely many:
plus `g = 6..15` and minus `g = 4..11`. They are ray-by-ray work, as in step 2.

## Decision

**Proceed, redirected:**

1. The uniform carrier is the core closure `C_q`, not a fit of the reachable
   graph. Containment `G_q ⊆ C_q` is all that Theorem A_B uses.
2. **Both stop conditions were checked and not met.** The minus middle table
   still holds at `g = 15, 16` (15 rays), and plus has a middle regime by
   `g = 16` (15 rays through `g = 20`).
3. Cover the leftover gaps (plus `6..15`, minus `4..11`) ray by ray with
   step 2's certificate. Done for plus `g = 6..10` and minus `g = 4..7` on
   reachable-graph carriers ([class-b-gap-rays-2026-10-27.md](class-b-gap-rays-2026-10-27.md));
   plus `11..15` and minus `8..11` remain.
4. Port the step-2 certificate engine to regime tables. That needs class
   A's [d-uniform machinery](class-a-gap-uniform-certificate-design-2026-10-23.md)
   with `g` in place of `d`: quadrant positivity in `(l, g)`, uniform division
   by `g`, and bivariate Perron signs. The core strictness thresholds above say
   the bivariate signs must be decided for `g ≥ 10` at least, and the gaps
   below the regime floors stay per-ray certificates or exact graphs.

**Stop condition** (checked 2026-10-27, not met). The regime route stops if the
minus middle table breaks at `g = 15, 16`, or if plus shows no middle regime by
`g = 20`. A future break is recorded as a negative control, and the route falls
back to per-gap rays.

## Evidence and replay

Floating-point exploration; nothing here is evidence for a claim.

```bash
# core-closure carrier of one member, as a .labels file
python oracles/python/class_b_core_closure.py carrier plus 13 60 out.labels
# containment of a native graph (labels from kernel/class_b_label_rays.mojo)
python oracles/python/class_b_core_closure.py contains plus 10 40 plus-g10-q40.labels
# negative control
python oracles/python/class_b_core_closure.py window plus 10 40 5 8
# regime profile over a directory of .labels files
python oracles/python/class_b_regime_probe.py DIR
```

`kernel/class_b_label_rays.mojo` now accepts `g ≤ 16`, `q ≤ 128`, so native
graphs for the containment checks can be exported beyond step 2's pilot range.

## Non-claims

No class-B member is certified here. Strictness is decided in double precision
with a `10⁻⁷` margin. The asymptotic threshold `g = 9` is a statement about
leading coefficients in `β`, not a finite-`q` proof. The regime fits are
finite: three gaps fit a table and the rest check it. Universal BH, A1′, #84,
G1 and PSC remain open.
