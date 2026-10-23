# Class A, gaps d>=5: boundary hitting for every n >= 5d, by d-uniform regime certificates (2026-10-23)

**Status:** repository-proved, computer-assisted, scoped to the class-A lines
`(n+d, n, n+eps)` of every gap `d >= 5` and both signs, for every member
`n = d l + r` with `l >= 5` (equivalently `n >= 5d`); independent human review
pending. On every such line every vertex of the complete canonical swap-seed
overlap graph has an offset-zero descendant. The strip `n < 5d` of every gap,
the class-C residual, universal #139/#84, G1 and PSC remain open. No ledger
claim is promoted; the status is that of the executable certificate.

## Stop/go and scope

The design is [class-a-gap-uniform-certificate-design-2026-10-23.md](class-a-gap-uniform-certificate-design-2026-10-23.md)
(Lemmas 1–4, 2', 3' and the regime vocabulary), decided at
[class-a-gap-uniformity-stopgo-2026-10-23.md](class-a-gap-uniformity-stopgo-2026-10-23.md);
gaps `d <= 4` are the residue-ray certificates of
[class-a-residue-rays-2026-10-22.md](class-a-residue-rays-2026-10-22.md) and
[class-a-d4-rays-2026-10-23.md](class-a-d4-rays-2026-10-23.md). Nothing is
imported from the literature beyond what those notes record. The
[rectangle countermodel](class-a-cover-obstruction-2026-10-21.md) and the
[d=1 to d=2 non-transfer theorem](class-a-residual-geometry-2026-10-22.md)
remain the standing controls.

A finite observation preceded the certificate: for every gap `5 <= d <= 20`
and both signs the exact complete graph of every member with `5 <= l <= 9`
has a label set that is a union of typed `k`-intervals whose endpoints are
affine in `l` **with the same table for every gap** of a residue regime
(`evidence/class-a-gap-labels-2026-10-23/`, `kernel/class_a_gap_regimes.mojo`).

## Regimes and the theorem

Residue regimes of a sign: low `r = j`, high `r = d - j`, middle
`j0 <= r <= d - j1`, each for every `l >= 5` and every `d >= d0`. The minus
sign has `J = 3` (low 0..2, high 1..3, middle `3 <= r <= d-4`), the plus sign
`J = 5` (low 0..4, high 1..5, middle `5 <= r <= d-6`). Every integer quantity
of the ray certificate becomes a form in `Z[l, d, r]` (Lemma 1, Lemma 2 with
Lemma 2' as fallback) and every Perron sign a polynomial in `(h, u = d h)`
whose sign on the box `(0,1/5) x (0,1/d0]`, restricted to the member hull
`E >= 5 u (1+h)` (Lemma 3'), Bernstein subdivision decides exactly.

**Theorem G (regimes).** For each fitted regime and every `l >= 5`, `d >= d0`
(the registered floor in `psc.class_a_gap_regime_tables.regime_floors`),
the complete swap-seed graph of `(n+d, n, n+eps)`, `n = d l + r`, lies in the
regime's carrier (`CLASS_A_REGIME_CLOSURE`) and every carrier label reaches
offset zero within `2l + c` inflations (`CLASS_A_REGIME_DESCENT`), with the
same tables for every gap.

**Theorem R' (finite gaps and exceptional rays).** Where a regime's registered
floor exceeds its fitted floor, every `(d, r)` in between is a ray certificate
on the regime's own tables from the least `l' >= 5` that accepts, with exact
complete graphs for `5 <= l < l'`. The seven plus residues reached by no
fitted regime, `(d, r) = (5,1), (5,2), (6,1), (6,2), (7,2), (7,3), (8,3)`,
carry their own generated tables (`kernel/psc/class_a_ray_d{5,6,7,8}p.mojo`)
and certify at `n0 = 26, 22, 31, 32, 44, 31, 43` (`l0 = 5, 4, 5, 5, 6, 4, 5`;
the one `l0 = 6` member `n = 37` is an exact graph).

**Corollary C (coverage).** `psc.class_a_gap_theorem.eventual_cover` proves
that the fitted regimes tile every residue of every gap `d >= 7` (minus) and
`d >= 11` (plus): low `0..J_low`, middle `j0..d-j1`, high `d-J_high..d-1` with
`j0 <= J_low + 1` and `j1 <= J_high + 1`. Below those gaps `residue_cover`
lists the covering regime or ray of every residue and refuses an uncovered
one. Hence, for each sign, every member `n = d l + r` with `d >= 5`, `l >= 5`
is in exactly one of: a regime at or above its floor (Theorem G), a finite
gap of a regime (Theorem R'), an exceptional ray (Theorem R'). Boundary
hitting holds at every one of them. `kernel/class_a_gap_theorem.mojo
certify-all 5` re-certifies the whole chain and prints
`CLASS_A_GAP_THEOREM eps=.. l>=5 d>=5 ...`.

## Results

Regimes (`class_a_gap_uniform.mojo certify EPS KIND J 5 D0`; the closure certifies from the registered floor, the descent already from the fitted floor; closure counts are those at the registered floor, where clip fallbacks count Lemma 2' uses together with undecided clips):

| sign | regime | fitted `d>=` | closure `d>=` | finite rays / exact graphs | rows | closure covered / gaps / clip fallbacks | pieces / targets / descents | depth `<=` |
| --- | --- | ---: | ---: | --- | ---: | --- | --- | --- |
| minus | `low:r=0` | 5 | 5 | 0 / 0 | 93 | 3,652 / 3,068 / 3,000 | 127 / 8 / 172 | `2l+9` |
| minus | `low:r=1` | 5 | 8 | 3 / 2 | 119 | 4,535 / 3,789 / 356 | 157 / 8 / 200 | `2l+7` |
| minus | `low:r=2` | 6 | 6 | 0 / 0 | 115 | 4,431 / 3,715 / 3,137 | 153 / 8 / 193 | `2l+6` |
| minus | `high:r=d-1` | 5 | 6 | 1 / 0 | 105 | 3,935 / 3,307 / 2,864 | 137 / 8 / 176 | `2l+8` |
| minus | `high:r=d-2` | 5 | 5 | 0 / 0 | 109 | 4,300 / 3,640 / 6,576 | 147 / 8 / 185 | `2l+7` |
| minus | `high:r=d-3` | 5 | 5 | 0 / 0 | 113 | 4,542 / 3,846 / 8,516 | 151 / 8 / 191 | `2l+6` |
| minus | `middle:3<=r<=d-4` | 7 | 7 | 0 / 0 | 115 | 4,459 / 3,743 / 9,165 | 153 / 8 / 191 | `2l+6` |
| plus | `low:r=0` | 5 | 5 | 0 / 0 | 84 | 3,676 / 3,112 / 2,434 | 128 / 8 / 176 | `2l+9` |
| plus | `low:r=1` | 7 | 7 | 0 / 0 | 96 | 3,827 / 3,197 / 1,163 | 138 / 8 / 171 | `2l+8` |
| plus | `low:r=2` | 8 | 8 | 0 / 0 | 100 | 3,995 / 3,341 / 1,483 | 140 / 8 / 174 | `2l+8` |
| plus | `low:r=3` | 9 | 9 | 0 / 0 | 100 | 3,957 / 3,307 / 1,893 | 140 / 8 / 170 | `2l+6` |
| plus | `low:r=4` | 10 | 10 | 0 / 0 | 98 | 3,861 / 3,225 / 2,111 | 138 / 8 / 168 | `2l+6` |
| plus | `high:r=d-1` | 5 | 5 | 0 / 0 | 74 | 3,262 / 2,774 / 2,227 | 110 / 8 / 143 | `2l+11` |
| plus | `high:r=d-2` | 5 | 5 | 0 / 0 | 76 | 3,424 / 2,920 / 3,085 | 112 / 8 / 146 | `2l+11` |
| plus | `high:r=d-3` | 6 | 6 | 0 / 0 | 88 | 3,687 / 3,139 / 3,555 | 122 / 8 / 153 | `2l+8` |
| plus | `high:r=d-4` | 8 | 8 | 0 / 0 | 92 | 3,673 / 3,091 / 2,791 | 132 / 8 / 162 | `2l+7` |
| plus | `high:r=d-5` | 9 | 9 | 0 / 0 | 96 | 3,831 / 3,213 / 3,333 | 136 / 8 / 166 | `2l+6` |
| plus | `middle:5<=r<=d-6` | 11 | 11 | 0 / 0 | 98 | 3,855 / 3,219 / 4,992 | 138 / 8 / 168 | `2l+6` |

Exceptional plus rays (own tables, `class_a_residue_ray.mojo certify D 1 R N0`):

| ray | floor `n0` | rows | `|C|` | closure covered / gaps | pieces / targets / descents | depth `<=` |
| --- | ---: | ---: | --- | --- | --- | --- |
| `n=5l+1` | 26 | 90 | `40l+92` | 3,518 / 2,934 | 132 / 8 / 165 | `2l+8` |
| `n=5l+2` | 22 | 90 | `40l+96` | 3,438 / 2,886 | 124 / 8 / 157 | `2l+8` |
| `n=6l+1` | 31 | 94 | `40l+96` | 3,693 / 3,077 | 136 / 8 / 170 | `2l+8` |
| `n=6l+2` | 32 | 94 | `40l+106` | 3,695 / 3,095 | 134 / 8 / 168 | `2l+8` |
| `n=7l+2` | 44 | 98 | `40l+114` | 3,885 / 3,249 | 138 / 8 / 173 | `2l+8` |
| `n=7l+3` | 31 | 94 | `40l+102` | 3,673 / 3,083 | 134 / 8 / 164 | `2l+7` |
| `n=8l+3` | 43 | 98 | `40l+110` | 3,839 / 3,209 | 138 / 8 / 169 | `2l+6` |

On every ray and regime: 9 real seeds in the carrier and 3 non-strict seed
candidates, 65 terminal splits.

Assembly receipts (`class_a_gap_theorem.mojo certify-all 5`, `theorem.log`):

```text
CLASS_A_GAP_THEOREM eps=-1 l>=5 d>=5 regimes 7 regimes_cover_from_d 7 finite_rays 4 exceptional_rays 0 exact_graphs 2 universal_139=false
CLASS_A_GAP_THEOREM eps=1 l>=5 d>=5 regimes 11 regimes_cover_from_d 11 finite_rays 0 exceptional_rays 7 exact_graphs 1 universal_139=false
```

The four minus finite rays are `(5,1)`, `(6,1)`, `(7,1)` (low `r=1`, uniform
from `d = 8`) and `(5,4)` (high `r=d-1`, uniform from `d = 6`); `(5,1)` and
`(6,1)` certify from `l = 6` with the member `l = 5` an exact graph, the
others from `l = 5`. The one plus exact graph is `n = 37` of `(7,2)`.

Finite observations (not claims): every descent table was generated from one
sample ray of its regime (`d` = the closure floor, `l = 5..12`) and then
accepted for every gap `d >= d0`, which is the first evidence that the
first-hit potentials, like the label sets, do not depend on the gap. Two plus
regimes (low `r=1`, `r=2`) were refused on the plain box and accepted within
the member hull (Lemma 3'): the refused margins were positive at every member
and changed sign only where the box exceeds the hull.

## Work shown

### Assumptions and hypotheses

The lines `sigma(x) = x y^(n+d) x`, `sigma(c) = c y^n x`, `sigma(y) = x y^(n+eps) c`
on the determinant-two PIP domain (`1 <= d <= 2n + 6 eps + 5`; every member
with `l >= 5`, `d >= 5` satisfies it). Canonical swap seeds, proper-prefix
occurrence indices, bottom-minus-top offsets, equal-letter offset-zero
termination, as in the gap-one notes. Regime hypotheses: `l0 = 5`; low
`0 <= j < d0`; high `1 <= j <= d0`; middle `j0 >= 0`, `j1 >= 1`,
`d0 >= j0 + j1`. The finite parts of the assembly run through the ray
certificate and the exact graphs, whose guards are `d <= 32` (`ALine.check`)
and `n <= 256` (`ALine.member`); every finite ray and exact graph used has
`d <= 11` and `n <= 143`.

### Derivation / reduction

The ray certificate with `(l, d, r)` symbolic: Lemma 1 decides gap forms on
`l >= l0`, `d >= d0` by four corner/slope conditions (soundness uses the "if"
direction only); the regime reduction decides `r`-affine forms at the
regime's `r` endpoints; Lemma 2 divides by `d` with a constant rounding
where one exists and Lemma 2' supplies one-sided bounds (a superset of the
realizable index range, counted as a clip fallback) where it does not;
Lemma 3 certifies Perron signs by Bernstein subdivision on closed cells of
the `(u, t)` box, Lemma 3' skipping cells outside the member hull
`E >= l0 u (1+h)`; Lemma 4 re-proves the eigen and elimination identities
coefficient-wise for each sign. Closure is the window/gap/terminal argument
of the plus-line note; descent is a non-negative `l`-affine potential that
strictly drops along one realizable child occurrence per piece.

### Evidence and replay

From `kernel/`:

```bash
pixi run --locked mojo run -I . class_a_gap_theorem.mojo certify-all 5
pixi run --locked mojo run -I . class_a_gap_theorem.mojo cover 1 16
pixi run --locked mojo run -I . class_a_gap_uniform.mojo certify -1 2 3 5
pixi run --locked mojo run -I . class_a_gap_uniform.mojo descent-floor 1 0 1 5 24
pixi run --locked mojo run -I . class_a_residue_ray.mojo certify 7 1 2 44
pixi run --locked mojo run -I . tests/test_class_a_gap_theorem.mojo
pixi run --locked mojo run -I . tests/test_class_a_gap_regime_descent.mojo
pixi run --locked mojo run -I . tests/test_class_a_residue_rays.mojo
```

From the repository root:

```bash
python oracles/python/class_a_carrier_closure.py 26 --ray 5,1,1
python oracles/python/class_a_descent_table.py GRAPHS/reg_e-1_k0_j0 25 --ray 5,-1,0 --nhi 60 --tail-floor 25 \
  --src kernel/psc/class_a_gap_regime_rows_minus.mojo --rows-fn rows_low0 --mojo /tmp/descents_minus.mojo
(cd evidence/class-a-gap-theorem-2026-10-23 && sha256sum -c SHA256SUMS)
```

The packet `evidence/class-a-gap-theorem-2026-10-23/` holds the theorem log,
the coverage report, both floor searches, the exceptional-ray certificates,
the native test logs, the generator logs and JSON tables, the Python oracle
lines for the exceptional rays, and the digests of every graph export used
(sample rays of the 18 regimes, the seven exceptional rays, and the `d = 2,
3, 4` regeneration exports). Graph exports are byte-identical to the
archived ones where both exist; the `d = 2, 3, 4` ray tables regenerate
byte-identically from fresh exports with the extended generator.

### Negative controls

A removed row, a shifted row endpoint, another regime's rows and an empty
middle regime refuse the regime closure; a removed descent row, a shifted
piece end, a swapped child piece, a descent on the target piece and a regime
without tables refuse the regime descent; a third sign and a non-positive
floor refuse the assembly, and an uncovered residue refuses `residue_cover`
(the assembly built before the exceptional rays were registered refused at
`(5, 1)`). Lemma 2 refuses every rounding that varies with `d` or `r`; the
plain box refuses the two plus regimes that the hull accepts; the generator
refuses an incomplete table and the `d <= 4` tables it regenerates are
byte-identical. The gap-one rectangle countermodel and the non-transfer
theorem stand.

### Non-claims / remaining gaps

- Nothing about members with `l < 5` (`n < 5d`): for each fixed `l <= 4` the
  label sets form another two-parameter family in `(d, r)` that has not been
  fitted; the PIP domain reaches down to `n ~ (d - 5 - 6 eps)/2`.
- Nothing about the class-C residual, universal #139/#84, G1 or PSC.
- The generated tables are proof targets; the certificates are the evidence.
  The generator's sample-ray heuristic is not a theorem about potentials.
- Lemma 2' may in principle report a false escape; it did not on any fitted
  regime, which the receipts record (`clip_fallbacks`, no escape).
- Independent human review pending.
