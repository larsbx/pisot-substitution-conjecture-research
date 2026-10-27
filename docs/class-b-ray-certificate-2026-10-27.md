# Class B's top layer, step 2: residue-ray certificates for gaps g ≤ 5 (plus) and g ≤ 3 (minus) (2026-10-27)

**Status:** repository-proved, computer-assisted, scoped to eight lines of
class B's top layer, each on its whole PIP domain:

- plus, `(p, q, r) = (3q + 12 − g, q, q + 1)`, `g = 1, …, 5`;
- minus, `(p, q, r) = (3q − g, q, q − 1)`, `g = 1, 2, 3`.

Independent human review is pending. On each line, every vertex of the
complete canonical swap-seed overlap graph has an offset-zero descendant. The
other top-layer lines (plus `g ≥ 6`, minus `g ≥ 4`), universal BH, A1′, #84, G1
and PSC remain open. No ledger claim is promoted; the status is that of the
executable certificate.

This is step 2 of the
[top-layer stop/go](class-b-top-layer-stopgo-2026-10-23.md), whose
step-1 condition (label sets affine in `l`, in the `(u, v, k)` basis) was met
on 2026-10-24.

## Stop/go and scope

No new literature check is needed. This is the "per-gap residue-ray
certificate" that the stop/go authorizes, with its prior-art table:

- **BBJS** needs unimodularity, and class B has `|det M| = 2`.
- **Minervino–Thuswaldner** gives no family result.
- **Akiyama–Gähler–Lee** needs trace ≤ 2, and class B's trace is `r + 3 ≥ 3`.
- **Barge's class** does not apply: there are 0 witnesses among the 708 PIP
  top-layer members with `g ≤ 12`, `q ≤ 40`.

The method is that of class A's residue rays
([class-a-residue-rays-2026-10-22.md](class-a-residue-rays-2026-10-22.md)),
in class B's own coordinates. Two features are new:

1. **A closed-form Perron geometry.** The `k` coefficient of the displacement
   is exactly `−gβ`.
2. **A q-free potential.** `X = |k| + b(type, sign k)` with `0 ≤ b ≤ 6` replaces
   the class-A affine pieces.

The [label-ray note](class-b-label-rays-2026-10-23.md) showed that envelopes
of first-hit depth do not give a strict potential: 202 selected shortest edges
fail on plus `g = 1`. That warning is respected here. The potential is not a
depth envelope; it is the least fixed point of the descent inequality, and the
certificate proves the descent symbolically for every `l`.

## Setting

Letters are `(x, c, y) = (0, 1, 2)`, with images

```text
sigma(x) = x y^p x,   sigma(c) = c y^q x,   sigma(y) = c y^r x,
r = q + eps,   p = 3q + 6 + 6 eps − g,   eps = ±1,   g ≥ 1.
```

A *ray* fixes `(eps, g, r0)` with `0 ≤ r0 < g`, and puts `q = g l + r0`.

**Perron relation.** The incidence matrix has columns `(2, 0, p)`, `(1, 1, q)`
and `(1, 1, r)`. Expanding along the `y` row gives

```text
chi(t) = (t−2)(t−1)(t−r) − q(t−2) − p t = A(t) − q t(t+1),
A(t)   = (t−2)(t−1)(t−eps) − (6 + 6 eps − g) t,
```

so the Perron root satisfies `q β(β+1) = A(β)`. `chi_q(t)` decreases in `q`
for `t > 0`, so `chi_{q0}(β_low) < 0` with `β_low = q0 + 3 + eps` puts `β_q`
above `β_low` for every `q ≥ q0`. Numerically, `β − q` lies in `(4.8, 5.1)`
on plus and `(2.4, 3.0)` on minus.

**Tile lengths.** A left eigenvector, scaled by `β + 1` and normalized at
`L_y = β(β+1)`, is

```text
L = (3β² + (3 + 3 eps − g) β + 3 eps,  (β+1)(β−eps),  β(β+1)).
```

The rows `c` and `y` give `β(L_y − L_c) = eps L_y`, and row `y` then gives
`L_x` after `q` is eliminated through `chi`. `check_line_identity` checks
`(L M)_j = β L_j` modulo `chi`, coefficient-wise.

**Displacement.** In the unimodular coordinates `u = 3k + c + y`,
`d = c − 3k`, the displacement of an integral bottom-minus-top offset
`w = (k, c, y)` is

```text
T(w) = (β+1)(u β − eps d) − g β k.
```

The coefficient of `k` is `L_x + 3L_c − 6L_y = −gβ` exactly, on both branches.
That is the closed form of step 1's growth direction `(1, 3, −6)`. A state is
a strict overlap iff `−L_bottom < T < L_top`.

## Lemmas

**Lemma 1 (elimination of `l`).** For integer polynomials `a, b`,
`g β(β+1) (a + l b) = g a β(β+1) + b (A − r0 β(β+1))`, because
`g l = q − r0`. So `sign(a + l b) = sign N(β)` for an integer polynomial `N`.

**Lemma 2 (interval sign).** Let `N` have degree `D`. If `H(h) = h^D N(1/h)`
does not vanish at `h = 1/β_low`, and has no root in `(0, 1/β_low]` by an exact
Sturm count, then `sign N(β)` is constant for every `β ≥ β_low`. That covers
every member `q ≥ q0`. Otherwise the certificate refuses.

**Lemma 3 (affine ray).** This is class A's lemma verbatim: `u ≤ v` for every
integer `l ≥ l0` iff `u_1 ≤ v_1` and `u(l0) ≤ v(l0)`.

**Lemma 4 (children).** The segments of `sigma(t)` are:

- FIRST: empty prefix; the child letter is `x` for `t = x`, `c` otherwise.
- RUN: the first letter, then `m` copies of `y`, `0 ≤ m < R(t)`; the child
  letter is `y`.
- LAST: the first letter, then the whole run; the child letter is `x`.

The run lengths are `R = (p, q, r)`. Write `w' = M w + prefix_b − prefix_t`.
For a segment pair with first-letter differences `dx, dc`:

```text
k' = u − k + dx,     d' = −2u + dc − 3dx,
u' = (4 + r) u − g k − eps d + 3dx + dc + (m_b − m_t).
```

Every value of `m_b − m_t` in the integer interval of the two segments is
attained. So for a target `u'`, with `k = k_lo + j`, the realizable parent
indices are `g j ∈ [base + Δ_lo − u', base + Δ_hi − u']`. Every run has
`l`-slope a multiple of `g` (`3g`, `g`, `g`), so this is `j ∈ [⌈·/g⌉, ⌊·/g⌋]`,
affine in `l` with integer coefficients. The child displacement is
`T' = β T + pos_b − pos_t` (`L` is a left eigenvector), and it increases in
both `u'` (slope `β(β+1)`) and `j` (`k'` decreases, slope `gβ`).

The independent BFS check: a floating-point rebuild of the graphs from the
seeds and Lemma 4 alone reproduces the native vertex sets exactly. It was run
at plus `g = 1` (`q = 9, 12`), plus `g = 3` (`q = 20`), minus `g = 2`
(`q = 19`) and minus `g = 3` (`q = 22`). This scratch check is reproduced in
canonical form by the replays below.

## Theorem A_B: uniform carrier closure

A carrier row `(top, bottom, u, d, a, b, c, e)` holds the labels with
`a l + b ≤ k ≤ c l + e`. The rows are those of
[`carriers.json`](../evidence/class-b-label-rays-2026-10-23/carriers.json),
fitted on 2026-10-23 and held out through `q = 42`.

**Theorem A_B.** For each tabulated ray and every member `q ≥ q0` on it:

1. every carrier label is a strict overlap;
2. the nine real swap seeds are carrier labels, and the other three seed
   candidates are not strict;
3. every real child of every non-terminal carrier label is a carrier label.

Hence `G_q ⊆ C_q`.

*Proof.* Fix the ray and `q0`.

- **(i)** `T` is affine in `j`, so the strictness of a row is two sign pairs
  at its ends (Lemmas 1–2).
- **(ii)** The twelve candidate seeds have constant labels.
- **(iii)** Fix a row and a segment pair.
  - *Window.* At `u' = ±6`, the child lies beyond the corresponding boundary
    at `j = 0` and at `j = J`, hence for all `j` and every `|u'| ≥ 6`.
  - *Gaps.* For `|u'| ≤ 5`, the realizable `j` (Lemma 4) are cut into covered
    intervals and gaps by the child slice's rows, which must be uniformly
    ordered. On a gap, `T'` increases in `j`, so one sign at one end shows
    that no child there is strict.
  - *Terminals and refusals.* The terminal `(t, t, 0)` is split out of every
    gap. An undecided order, sign or terminal membership refuses, and a strict
    child in a gap is an escape.

Induction on the inflation depth completes the proof. `square`

When a realizability bound is incomparable with the row ends, the range is
widened to `[0, J]`. That only adds gaps to exclude (`clip_fallbacks`). A gap
that is empty for some `l` only is still decided by its end signs, which hold
for every `l`.

## Theorem B_B: uniform descent

A potential row `(top, bottom, u, d, s, b)` assigns every label of that slice
with `sign k = s` the integer `X = |k| + b`, where `b ≥ 0`. The *targets* are
the offset-zero labels `w = 0`.

**Theorem B_B.** For each tabulated ray, every `q ≥ q0` and every non-target
carrier label `v`, there is a realizable child of `v` that is a carrier label
and satisfies `X(child) ≤ X(v) − 1`. So `v` reaches offset zero within `X(v)`
inflations.

*Proof.*

- **Pieces.** Split each row into its sign regions `k < 0`, `k = 0` and `k > 0`;
  each region is an affine `j`-interval, and an undecided region refuses.
  Within a piece, `X = s(k_lo + j) + b` is affine.
- **Candidates.** For every segment pair, every `|u'| ≤ 5`, every child row of
  the child slice and every child sign region `t`, intersect four affine
  intervals:
  - the piece;
  - the realizable range of Lemma 4;
  - the preimage `kc − K_hi ≤ j ≤ kc − K_lo` of the child row;
  - the child sign region.

  If the intersection is uniformly nonempty, the child of every `j` in it is
  real: it is realizable and it is a carrier label, which is strict by
  Theorem A_B (i).
- **Descent check.** `D(j) = X_parent − X_child − 1 = s(k_lo + j) + b −
  t(kc − j) − b' − 1` is affine in `j` and `l`. It is checked to be at least 0
  at both ends of the candidate interval, for every `l ≥ l0` (Lemma 3).
- **Cover.** A greedy cursor covers each piece by descending candidates; a
  piece left uncovered refuses.
- **Termination.** `X` is a non-negative integer that strictly decreases along
  the chosen children. Only a target has no descent requirement, so the path
  ends at offset zero. `square`

**Corollary L_B (eight top-layer lines).** On each of the eight lines above,
every vertex reachable from the three swap seeds has an offset-zero descendant,
for every PIP member:

- members `q ≥ q0` by Theorems A_B and B_B on their ray (each line's residues
  are all tabulated);
- members below `q0` by the exact uncapped complete graph (mode `below`,
  `q ≤ 21`).

The consequences then follow exactly as for Theorem C
([p1b-symbolic-cone-2026-10-08.md](p1b-symbolic-cone-2026-10-08.md) §4):

- Corollary E2 gives SC_all on class B;
- manuscript Corollary `cor:scc-reduction`(ii) and Theorem `thm:main-density`
  give pure discrete spectrum;
- Proposition `prop:G1-from-half-coincidences` gives G1.

The status is the same: repository-proved, computer-assisted, human review
pending. Nothing beyond BH from every seed is used as input to that chain.

## Results

The tables are `kernel/psc/class_b_ray_tables.mojo`, generated by
`oracles/python/class_b_ray_tables.py`. The 21 rays, with the counts of both
verifiers:

| Branch | `g` | ray | `q0` | rows | `(row, segments, u′)` cases with range / gaps | descent pieces / intervals | `max b` | replay `|G_q|` at first two members | exact members below `q0` |
| --- | ---: | --- | ---: | ---: | --- | --- | ---: | --- | ---: |
| plus | 1 | `q=1l+0` | 9 | 389 | 14,241 / 10,255 | 637 / 1,021 | 6 | 2765 (`q=9`), 2877 (`q=10`) | 6 |
| plus | 2 | `q=2l+0` | 12 | 303 | 10,527 / 7,799 | 539 / 739 | 5 | 1627 (`q=12`), 1739 (`q=14`) | 4 |
| plus | 2 | `q=2l+1` | 11 | 297 | 10,373 / 7,677 | 533 / 729 | 5 | 1573 (`q=11`), 1685 (`q=13`) | 3 |
| plus | 3 | `q=3l+0` | 12 | 263 | 9,167 / 6,879 | 475 / 589 | 4 | 1065 (`q=12`), 1177 (`q=15`) | 2 |
| plus | 3 | `q=3l+1` | 16 | 287 | 9,769 / 7,287 | 499 / 625 | 4 | 1251 (`q=16`), 1363 (`q=19`) | 3 |
| plus | 3 | `q=3l+2` | 14 | 273 | 9,285 / 6,973 | 485 / 609 | 4 | 1131 (`q=14`), 1243 (`q=17`) | 3 |
| plus | 4 | `q=4l+0` | 16 | 265 | 8,775 / 6,635 | 447 / 541 | 4 | 935 (`q=16`), 1047 (`q=20`) | 2 |
| plus | 4 | `q=4l+1` | 17 | 247 | 8,225 / 6,227 | 429 / 513 | 4 | 921 (`q=17`), 1033 (`q=21`) | 2 |
| plus | 4 | `q=4l+2` | 18 | 251 | 8,519 / 6,467 | 433 / 523 | 4 | 971 (`q=18`), 1083 (`q=22`) | 3 |
| plus | 4 | `q=4l+3` | 15 | 271 | 9,025 / 6,829 | 453 / 543 | 4 | 927 (`q=15`), 1039 (`q=19`) | 2 |
| plus | 5 | `q=5l+0` | 20 | 261 | 8,757 / 6,562 | 420 / 502 | 4 | 858 (`q=20`), 970 (`q=25`) | 2 |
| plus | 5 | `q=5l+1` | 16 | 255 | 8,499 / 6,366 | 414 / 492 | 4 | 740 (`q=16`), 852 (`q=21`) | 1 |
| plus | 5 | `q=5l+2` | 17 | 243 | 8,215 / 6,158 | 402 / 484 | 4 | 762 (`q=17`), 874 (`q=22`) | 2 |
| plus | 5 | `q=5l+3` | 18 | 239 | 7,915 / 5,956 | 398 / 478 | 4 | 748 (`q=18`), 860 (`q=23`) | 2 |
| plus | 5 | `q=5l+4` | 19 | 235 | 7,937 / 5,970 | 394 / 470 | 4 | 784 (`q=19`), 896 (`q=24`) | 2 |
| minus | 1 | `q=1l+0` | 15 | 417 | 14,313 / 10,385 | 576 / 811 | 6 | 2279 (`q=15`), 2391 (`q=16`) | 6 |
| minus | 2 | `q=2l+0` | 18 | 228 | 8,252 / 6,201 | 414 / 546 | 4 | 1306 (`q=18`), 1418 (`q=20`) | 4 |
| minus | 2 | `q=2l+1` | 17 | 218 | 7,996 / 6,009 | 404 / 542 | 4 | 1300 (`q=17`), 1412 (`q=19`) | 3 |
| minus | 3 | `q=3l+0` | 21 | 220 | 7,750 / 5,901 | 406 / 504 | 4 | 940 (`q=21`), 1052 (`q=24`) | 3 |
| minus | 3 | `q=3l+1` | 22 | 236 | 8,266 / 6,269 | 422 / 530 | 4 | 1068 (`q=22`), 1180 (`q=25`) | 3 |
| minus | 3 | `q=3l+2` | 20 | 222 | 7,984 / 6,061 | 408 / 516 | 4 | 944 (`q=20`), 1056 (`q=23`) | 3 |

Common to every ray:

- 9 real seeds and 3 non-strict seed candidates;
- 8 target pieces, the offset-zero labels;
- 86 terminal splits (89 on minus `g = 1`);
- 112 new labels per `l`-step.

**Floors.** A floor `q0` is the fitted label floor of `carriers.json`, except
on minus `g = 3`. There, at the fitted floors 18, 16 and 17, an affine maximum
or minimum is undecided, and the certificate first accepts at 21, 22 and 20.
Below a floor the certificate refuses. That is the fail-closed outcome, not a
counterexample, and those members are exact graphs.

**What the potential looks like.** `b` is the least fixed point of
`b[P] = max_{v ∈ P} (1 + min_child X(child) − |k_v|)`, iterated from `b = 0`
on two exact graphs of the ray (`q = q0 + 2g` and `q0 + 3g`), and `max b ≤ 6`.
It is tight where tested: on plus `g = 1`, lowering each of 10 sampled positive
entries refuses, and so does the zero table. It is not uniform across rays,
with 466 of the 1,017 type keys conflicting. The first-hit depth is observed to be close to `|k|/2 + O(1)`,
independently of `q` (finite observation, plus `g = 1`, `q = 20..42`). So `X`
over-counts depth by about a factor of 2 and needs no `l` term at all.

## Work shown

### Assumptions and hypotheses

- The eight class-B lines above, with `q = g l + r0`.
- The members are those of the open top layer, checked by
  `BRay.check_domain` at every floor. For `q ≥ q0` every member is in the
  open top layer, since the defining inequalities reduce to `q > g + 1`,
  `q > 2g − 14` (plus) and `q > g + 7`, `q > 2g − 5` (minus).
- The objects are canonical swap seeds, proper-prefix occurrences,
  bottom-minus-top integral offsets, and equal-letter offset-zero terminals.
  Targets are all offset-zero labels, as in class A.
- No hypothesis is added. Pisot-ness is not used by the certificate, only by
  the consequences.

### Derivation / reduction

- The Perron relation, the lengths, the closed-form `T` with its `−gβ`
  coefficient, and Lemmas 1–4 are derived above.
- Theorems A_B and B_B reduce every question to finitely many integer
  polynomial signs on `(0, 1/β_low]` and affine comparisons on `l ≥ l0`.
- The certificate checks `L` as a left eigenvector modulo `chi`, and
  `chi_{q0}(β_low) < 0`, before using either.
- The Python verifier re-derives `chi = A − q t(t+1)` from the incidence
  matrix it reads off the image words.

### Evidence and replay

From `kernel/`:

```bash
pixi run --locked mojo run -I . -I tests tests/test_class_b_ray_certificate.mojo
pixi run --locked mojo build -I . class_b_ray_certificate.mojo -o build/class-b-ray-certificate
build/class-b-ray-certificate all
```

From the repository root:

```bash
python oracles/python/class_b_ray_certificate.py
python oracles/python/class_b_ray_tables.py --check
python -m pytest -q tests/test_class_b_ray_certificate.py
(cd evidence/class-b-ray-certificate-2026-10-27 && sha256sum -c SHA256SUMS)
```

The packet is
[`evidence/class-b-ray-certificate-2026-10-27/`](../evidence/class-b-ray-certificate-2026-10-27/).

- **Both verifiers.** The Mojo certificate (`all`) and the independent Python
  verifier report identical counts on all 21 rays.
- **Replays.** `all` replays each ray at its first two members, where the
  native graph equals the carrier and every native vertex has a native edge
  that lowers `X`.
- **Below the floors.** It also builds every member of the line below the
  floor, as exact graphs.
- **CI.** `.github/workflows/class-b-ray-certificate.yml` reruns all of this
  and diffs the two count streams.

### Negative controls

In the Mojo test (plus `g = 1`), and repeated in pytest:

- removing a carrier row (row 68, or row 0) is refused;
- lowering one positive potential constant leaves a piece with no descent;
- the zero table and a missing potential row refuse;
- another ray's carrier (minus `g = 1`) refuses on plus `g = 1`, and plus
  `g = 1`'s carrier refuses on minus `g = 1`;
- certifying below a floor refuses, at plus `g = 1` `q0 = 8` and minus
  `g = 3` `q0 = 19`;
- an off-ray parameter, a member outside the top layer and `eps = 0` refuse;
- wrong image words make the oracle's Perron derivation refuse.

In the prototype stage, deleting each of 12 random rows on plus `g = 1` was
refused every time.

### Non-claims / remaining gaps

- **Lines.** Only these eight lines are certified. The top layer for each `q`
  has `g` up to about `q/2`, so infinitely many lines remain: plus `g ≥ 6`,
  minus `g ≥ 4`. The g-uniform regime certificate (step 2b of the stop/go)
  is not attempted.
- **Not uniform.** The per-ray potentials are not uniform in `g`, and no
  claim is made that one table serves all gaps.
- **Open.** Universal BH, A1′, #84, G1 and PSC remain open.
- **Observations, not claims.** The depth ≈ `|k|/2` observation and the
  equality of carrier and graph beyond the replayed members are finite
  observations; only containment is proved.
- **Not formalized.** Nothing here is Lean-formalized, and independent human
  review is pending.
