# Class A, gaps d>=5: stop/go for a certificate uniform in the gap (2026-10-23)

**Status:** stop/go and design note with an exact finite profile; no theorem.
The residue-ray certificate now covers every class-A gap `d<=4` on both signs,
each line on its whole domain ([residue rays](class-a-residue-rays-2026-10-22.md),
[d=2 plus](class-a-d2-plus-rays-2026-10-22.md), [d=4](class-a-d4-rays-2026-10-23.md)).
What remains of class A is one line `(n+d, n, n+eps)` per gap `d>=5`, an
infinite family that ray-by-ray tabulation cannot exhaust. This note records
the proposed target, prior art, what the exact graphs show, and the decision.

## Proposed claim

For each sign `eps`, and for every gap `d>=d0` and every `n` in the PIP domain
of `(n+d, n, n+eps)`, every vertex of the complete canonical swap-seed graph
has an offset-zero descendant. The proof would be **one** certificate,
quantified over `(l, d, r)` with `n = d l + r`, not one per gap.

## Prior art and transfer

| Source | What it gives | Transfers? |
| --- | --- | --- |
| Barge, *Pure discrete spectrum in substitution tiling spaces* ([arXiv:1107.3598](https://arxiv.org/abs/1107.3598)); Akiyama–Barge–Berthé–Lee–Siegel, *On the Pisot substitution conjecture* | balanced-pair termination with coincidence from one seed pair characterizes pure discrete spectrum for irreducible Pisot substitutions | the repository's boundary-hitting reduction already rests on this; nothing new |
| Berthé–Bourdon–Jolivet–Siegel, *A combinatorial approach to products of Pisot substitutions*, ETDS 36 (2016) ([arXiv:1401.0704](https://arxiv.org/abs/1401.0704)) | the closest construction: a generic algorithmic proof of pure discrete spectrum for **infinite families**, given as finite products of three-letter (Brun, Jacobi–Perron) substitutions, via discrete planes and dual substitutions | **no.** Discrete planes and dual substitutions need unimodularity, and class A has determinant two. The idea of a finite combinatorial certificate covering an infinite family does carry over |
| Minervino–Thuswaldner, *The geometry of non-unit Pisot substitutions*, Ann. Inst. Fourier 64 (2014) ([arXiv:1402.2002](https://arxiv.org/abs/1402.2002)) | non-unit Rauzy fractals in adelic space | already in the run-index stop/go; no family result |
| Akiyama–Gähler–Lee (three letters, trace <= 2); Hollander–Solomyak (two letters) | complete finite or two-letter results | class A has trace `2 + 1 + (q+s) = q+s+3 >= 3`, outside the trace bound for every member |

No source states a coincidence or pure-discrete-spectrum theorem for these
lines or for any non-unit two-parameter family. Novelty would lie in the
certificate, not in the reduction.

## Exact finite profile

`kernel/class_a_residue_ray.mojo profile D EPS 64` builds the exact complete
graph of every member with `n <= 64`. It fits each residue ray's vertex count
as `slope*l + c(d,r)` from its two largest members with `l>=2`, and flags
whether every such member lies on the fit. Packet:
`evidence/class-a-gap-profile-2026-10-23/` (`d = 1..16`, both signs). On every
tabulated ray (`d<=4`), the profile equals the proved carrier cardinality
(`kernel/tests/test_class_a_gap_profile.mojo`). Every graph hits, and the
largest first-hit depth falls with `d`: 46 at `d=1`, 5–9 for `d>=8`
(`n<=64`).

Once `d` is large enough for the window `n <= 64` to reach the stable
regime, the constants settle (slope 40 throughout):

| `eps` | `r=0` | `r=1` | `r=2` | `r=3` | middle `r` | `d-5` | `d-4` | `d-3` | `d-2` | `d-1` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `-1` (`d>=7`) | 73 | 147 | 139 | 139 | 139 | 139 | 139 | 135 | 127 | 123 |
| `+1` (`d>=12`) | 86 | 98 | 118 | 114 | 112 | 108 | 100 | 96 | 86 | 90 |

Two limitations:
- **Flags and the l-threshold.** A profile flag (`affine 0`) means that not
  every member with `l>=2` lies on the fit. The proved rays need `l>=4..7`
  (floors 13–25 at `d=2..4`), so the flags record an l-threshold, not a
  break. The window `n<=64` reaches `l>=7` only for `d<=9`. At `d>=14` it
  holds `l=2..4` only, and the fits there (slopes 26–38) are pre-threshold
  artefacts. The table above is read off `d<=13`, where the middle values
  are already constant. The next experiment needs `n` up to about `8d` per
  gap.
- The table counts vertices only. Whether the **label sets** themselves
  (row endpoints) are affine in `(l, d, r)` per regime is the next
  experiment; counts do not decide it.

### Why there are regimes

In the residue-ray child index, a fixed child `y'` has realizable rows
`d j in [y' - B - Delta_hi, y' - B - Delta_lo]` with
`B = d k_lo + n s + eps y` and `n s = d l s + r s`. So `j` is a translate
(affine in `l`) of `ceil((c - r s)/d)` or `floor(...)`, for constants `c`
drawn from the finitely many bounded y-offsets, run-position constants and
`y' in -4..4`. For `s = +-1` that rounding is the same for all `r` with
`|c| < r < d - |c|`. It changes only when `r` is within a bounded distance
of `0` or of `d`. This gives finitely many boundary regimes (`r = j` and
`r = d - j` for small fixed `j`) and one middle regime, which is what the
profile shows. The mechanism is a derivation sketch, not yet a check.

## Design of a d-uniform certificate

The existing certificate is affine in one parameter `l` with Perron signs in
`h` alone. A d-uniform version needs three changes:

1. **Parameters.** Rows, pieces and descent occurrences become affine in
   `(l, d)` on each boundary regime (`r = j` or `r = d - j`, fixed `j`). On
   the middle regime they are affine in `(l, d, r)` over the polyhedral region
   `{l >= l0, d >= d0, j0 <= r <= d - j1}`. An affine form is non-negative on
   that region iff it is non-negative at its vertex and along its finitely
   many extreme rays, which is an exact integer check. It replaces today's
   comparison in `l` alone.
2. **Perron signs in two variables.** Eliminating `n` by
   `n h(1+h) = 1 - eps h - (d+1-eps) h^2 - d h^3` leaves margins that are
   polynomials in `h` with coefficients affine (or low-degree) in `d`. Put
   `u = d h`. Since `n >= d l`, we have `h <= 1/n <= 1/(d l0)`, hence
   `u <= 1/l0` and `h <= 1/n0`. Every margin becomes a polynomial in `(h, u)`
   on the box `(0, 1/n0] x (0, 1/l0]`. Its sign is certified exactly by the
   signs of Bernstein coefficients after subdivision, with rational
   arithmetic only and refusal on an undecided cell. This replaces the
   one-variable Sturm count.
3. **Rounding regimes.** The `ceil/floor(./d)` of fact 2 is resolved per
   regime by the bounds on `r`, as above, rather than by divisibility of an
   `l`-slope.

**Decision: proceed, narrowed.** The next experiment has three steps:
- **(a)** extend the table generator to fit carrier rows per regime, affine
  in `(l, d)` (boundary regimes) and `(l, d, r)` (middle), from exports at
  `d = 8..20`. A failed fit is a recorded refutation of the regime ansatz;
- **(b)** only if (a) fits, implement the bivariate Bernstein sign lemma and
  the polyhedral comparisons in Mojo, with negative controls;
- **(c)** port closure and descent to the three-parameter tables.

The stop conditions are: (a) fails; label sets carry an `r`-dependence that is
not affine; or a two-variable margin is undecidable on every subdivision near
a box corner. Each of these would redirect the work to a different
parametrization, for example `m = n - d l` with `d` unbounded.

## Step (a) result (2026-10-23): the regime fit holds

`kernel/class_a_gap_regimes.mojo build D EPS 5 9 DIR` recorded the exact
complete graph of every member `n = d l + r`, `5 <= l <= 9`, of both lines
for `d = 1..16`, and of the plus line at `d = 17` (the minus line at `d = 17`
has 80 of 85 members; `d = 18..20` are not started). The run uses
`parallel_fold` workers and stores labels as typed k-intervals.
`fit EPS DIR 5 16 J 5 OUT` then fitted every row endpoint of every regime
exactly over Q.

| sign | J | regimes fitted (least gap) | middle regime |
| --- | --- | --- | --- |
| `-1` | 3 | `r=0,1` (5), `r=2` (6); `r=d-1,d-2,d-3` (5) | `3<=r<=d-4`: 10 gaps, 275 members, 115 rows, rank 5 |
| `+1` | 5 | `r=0..4` (5,7,8,9,10); `r=d-1..d-5` (5,5,6,8,9) | `5<=r<=d-6`: 6 gaps (`d=11..16`), 105 members, 98 rows, rank 5 |

**Coverage.** For the minus line, every `(d, r)` with `d >= 5` lies in a
fitted regime. For the plus line, every `(d, r)` with `d >= 11` does. The
remaining plus residues at `d = 5..10` are finitely many and suit ray-by-ray
tables, as for `d = 4`.

**Sensitivity.** `J = 4` (minus) and `J = 6` (plus) also fit. `J = 3, 4`
(plus) refuse: the middle row count changes (`fit-eps1-J4.log`).

**Simplification.** No fitted endpoint uses `n`, `d` or `r`, only `l` and the
constant. Every fit has full rank (4 on boundary regimes, 5 on the middle), so
those zeros are determined, not chosen. In the k-coordinates, each regime's
label set is the **same `l`-affine table for every gap** `d >= d_min`. A
d-uniform certificate therefore needs one table per regime, of the existing
ray-table shape. Design item 1 (affine forms over a polyhedral
`(l, d, r)`-region) reduces to comparisons in `l`. Design item 2 is now the
whole new obligation: Perron margins as polynomials in `(h, u = d h)` with `d`
unbounded, and the child-index rounding by `d`.

**Decision:** continue to step (b), the bivariate sign lemma, with the 18
regime tables in `evidence/class-a-gap-labels-2026-10-23/fits/` as targets.
They are finite observations on `l = 5..9`, `d <= 16`. No certificate exists
yet, and no theorem about any gap `d >= 5` is claimed.

## Non-claims

- No theorem about any gap `d >= 5`.
- The regime table is a finite observation, for `d <= 16` and `n <= 64`.
- The prior-art table summarizes abstracts and the repository's earlier
  stop/go; it is not a full literature review of the class-C residual or of
  #139.
- The cap on `d` in `ALine` rises from 8 to 32. This is a budget change only,
  so the profile can run.
- Independent human review pending.
