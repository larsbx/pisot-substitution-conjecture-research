# Class A: residue-ray certificates and boundary hitting on gaps d=2 (minus) and d=3 (both signs) (2026-10-22)

**Status:** repository-proved, computer-assisted, scoped to three determinant-two
class-A lines: `(n+2,n,n-1)` for every `n>=2`, `(n+3,n,n-1)` for every `n>=2`
and `(n+3,n,n+1)` for every `n>=1`, i.e. each of these lines on its whole
determinant-two PIP domain (`(3,0,1)` lies on the previously certified line
`p=2q+3`); independent human review pending. On each line every vertex of
the complete canonical swap-seed overlap graph has an offset-zero descendant.
Other gaps, the plus line `d=2` (owned by PRs #312–#314, #318, #319), the
class-C residual, universal #139/#84, G1 and PSC remain open. No ledger claim
is promoted; the status is that of the executable certificate.

## Stop/go and scope

The literature decision of [p1b-class-a-run-index-2026-10-21.md](p1b-class-a-run-index-2026-10-21.md)
(Akiyama–Lee, Minervino–Thuswaldner, Barge) covers all of determinant-two class
A; nothing is imported. The method is that of the gap-one certificates
([plus line](class-a-carrier-closure-2026-10-22.md), [minus line](class-a-minus-line-2026-10-22.md)),
extended to gaps `d>=2` by residue rays. The repository precedent for
residue stratification is the `n mod 4` parity carrier of the `d=2` plus line
([class-a-d2-uniform-child-closure-2026-10-22.md](class-a-d2-uniform-child-closure-2026-10-22.md));
that line is not re-proved here. The [rectangle countermodel](class-a-cover-obstruction-2026-10-21.md)
and the [d=1 to d=2 non-transfer theorem](class-a-residual-geometry-2026-10-22.md)
remain the standing controls: every check is at typed-label level and no gap-one
carrier is transplanted.

Before building, a finite probe of `d=2,3`, both signs, `n=4..30` found every
state hitting and, with `n = d l + r`, every label set an exact union of
intervals with endpoints affine in `l` (from `n>=8`; `d=3` minus from
`n>=11`), while no fit affine in `n` exists. Decision: **proceed** with a
single residue-ray certificate rather than a per-line implementation.

## Residue rays

Lines `sigma(x)=x y^(n+d) x`, `sigma(c)=c y^n x`, `sigma(y)=x y^(n+eps) c`. With
`h=1/(beta-1)` and #311's two-sign geometry,

```text
P(n,h) = 1 - (n+eps) h - (n+d+1-eps) h^2 - d h^3,      n h(1+h) = 1 - eps h - (d+1-eps) h^2 - d h^3,
L = (1 + (d+1-eps) h + d h^2, 1 + (1-eps) h, 1 + h),   T(w) = s L_c + k d h(1+h) + y eps h.
```

`n^3 P(n,1/n) = -(1+eps) n^2 - (d+1-eps) n - d < 0` for both signs, so
`(0,1/n0]` contains `h_n` for all `n>=n0` (re-proved exactly per run). A *ray*
fixes `(d,eps,r)`, `0<=r<d`, and writes `n = d l + r`. Three facts make the
gap-one certificate go through on a ray:

1. **Scaling.** `d (a l + b) = a n + (d b - a r)`. Every displacement and tile
   length is multiplied by the same `d>0` (`ALine.to_n`), so each Perron sign
   is again the sign of `A(h) + n B(h)` and Lemmas 1–2 of the plus-line note
   (elimination of `n`, Sturm sign on `(0,q]`) apply verbatim.
2. **Child index.** `M w = (k+s, s-k, n s + d k + eps y)`, so
   `y' = d k_lo + n s + eps y + d j + (m_b - m_t)`. For fixed `y'` the
   realizable row indices are `d j in [y' - B - Delta_hi, y' - B - Delta_lo]`,
   with `B = d k_lo + (d l + r) s + eps y` and run differences `Delta` whose
   `l`-slopes are multiples of `d` (runs have length `d l + const`). Hence
   `j in [ceil(./d), floor(./d)]`, again affine in `l` with integer
   coefficients (`a_div_ceil`, `a_div_floor`; a non-divisible slope refuses).
3. **Monotonicity.** `T'` increases in `j` (slope `d h(1+h)`) and in `y'`
   (slope `L_y = 1+h`), so the window, gap and end-point arguments of
   Theorems A/B of the plus-line note hold unchanged, with Lemma 3 on the
   integer ray `l >= l0`.

For `d=1` (`l=n`, `r=0`) this is literally the old certificate: the gap-one
plus and minus native logs, oracle JSONs and generated tables are
byte-identical to their archived packets.

## Results

Rows, pieces and descents per ray are in `kernel/psc/class_a_ray_d2m.mojo`,
`class_a_ray_d3m.mojo`, `class_a_ray_d3p.mojo`; the registry
`kernel/psc/class_a_ray_tables.mojo` records the floors.

| Line | ray | floor | rows | `|C|` | closure cases covered / gaps | pieces / targets / descents | depth `<=` |
| --- | --- | ---: | ---: | --- | --- | --- | --- |
| `(n+2,n,n-1)` | `n=2l` | 14 | 97 | `40l+93` | 3,869 / 3,278 | 145 / 8 / 208 | `2l+9` |
| `(n+2,n,n-1)` | `n=2l+1` | 15 | 111 | `40l+149` | 4,361 / 3,710 | 157 / 8 / 221 | `2l+8` |
| `(n+3,n,n-1)` | `n=3l` | 15 | 93 | `40l+81` | 3,652 / 3,061 | 129 / 8 / 182 | `2l+9` |
| `(n+3,n,n-1)` | `n=3l+1` | 19 | 113 | `40l+143` | 4,404 / 3,713 | 153 / 8 / 204 | `2l+7` |
| `(n+3,n,n-1)` | `n=3l+2` | 20 | 105 | `40l+131` | 4,062 / 3,429 | 139 / 8 / 188 | `2l+8` |
| `(n+3,n,n+1)` | `n=3l` | 18 | 88 | `40l+94` | 3,392 / 2,857 | 134 / 8 / 184 | `2l+9` |
| `(n+3,n,n+1)` | `n=3l+1` | 16 | 84 | `40l+94` | 3,238 / 2,741 | 124 / 8 / 162 | `2l+11` |
| `(n+3,n,n+1)` | `n=3l+2` | 17 | 78 | `40l+98` | 3,026 / 2,569 | 116 / 8 / 157 | `2l+11` |

On every ray: 9 real seeds in the carrier and 3 non-strict seed candidates,
65 terminal splits, no conservative clip at the floor.

**Theorem R.** For each tabulated ray and every `n >= floor` on it, the
complete swap-seed graph lies in the ray's carrier (closure) and every
carrier label reaches offset zero within the stated depth (descent).

**Corollary L.** On each of the three lines, every vertex of the complete
swap-seed graph has an offset-zero descendant, for every `n` in the line's
domain: for `n` at or above its ray's floor by Theorem R, below it by the
exact complete graph (`n<=19`, all depths finite, cap not reached).

Finite observations (not claims): the carrier equals the graph label set on
every export used for fitting (by construction) and is re-checked against the
exact graph at the first two members of every ray; e.g. `|G_n| = 20n+93` and
`20n+129` on the two `d=2` minus rays. A floor is the least `n` of its ray at
which both certificates are accepted. Below it they refuse (an undecided
Sturm sign, a vanishing interval bound, or a table piece of negative length),
which is the fail-closed outcome, not a counterexample.

## Work shown

### Assumptions and hypotheses

The three normal-form lines above on the determinant-two PIP domain of the
run-index note (`1<=d<=2n+6eps+5`, checked by `check_domain` at every floor;
every finite member is re-screened). Canonical swap seeds, proper-prefix
occurrence indices, bottom-minus-top offsets, equal-letter offset-zero
termination, as in the gap-one notes.

### Derivation / reduction

Facts 1–3 above reduce each ray to the gap-one proof: Lemma 1 (elimination),
Lemma 2 (Sturm sign on `(0,1/n0]`), Lemma 3 (affine comparisons in `l`),
Lemma 4 with the child index of Fact 2, then Theorem A (closure by window,
gap and terminal cases) and Theorem B (non-negative potential strictly
decreasing along chosen occurrences). The eigen identity
`h M^T L - (1+h) L = -P(1,1,1)` and the elimination are checked
coefficient-wise for each `(d,eps)`; the Python verifier re-derives `P` from
the characteristic polynomial of the incidence matrix read off the images.

### Evidence and replay

From `kernel/`:

```bash
pixi run --locked mojo run -I . tests/test_class_a_residue_rays.mojo
pixi run --locked mojo run -I . class_a_residue_ray.mojo certify 3 -1 1 19
pixi run --locked mojo run -I . class_a_residue_ray.mojo survey 3 1 30
```

From the repository root:

```bash
python oracles/python/class_a_carrier_closure.py 19 --ray 3,-1,1
python -m pytest -q tests/test_class_a_residue_rays.py
(cd evidence/class-a-residue-rays-2026-10-22 && sha256sum -c SHA256SUMS)
```

Packet: `evidence/class-a-residue-rays-2026-10-22/`. The Mojo certificate and
the independent Python verifier report identical closure and descent counts on
all eight rays.

### Negative controls

Per ray: removing a carrier row is an escape; the carrier of the next residue
does not fit; a raised child potential, a mislabelled child `y'` and a missing
descent row refuse. A residue outside `0..d-1`, a parameter off its ray and an
affine slope not divisible by `d` refuse. Below each floor the certificate
refuses (recorded in the table above as the floor). The generator alone
needed two widenings for `d=1` minus (recorded in the side-notes ledger) and
none further; on six of the eight rays it uses the one-step slack fit
(`depth <= floor(X/3) <= depth+1`) on one target row.

### Non-claims / remaining gaps

Only the three lines above. The `d=2` plus line is the subject of open PRs
#318/#319 and is deliberately not tabulated here. Gaps `d>=4`, the rest of the
class-A residual, the class-C residual `d>=4`, aligned #138, universal
#139/#84, G1 and PSC are open. The finite-survey formulas are observations;
the generator is not evidence. Not Lean-formalized; independent human review
pending. The `ALine` remark of the minus-line note that only `d=1` is
represented is superseded by this note.

**Addendum (2026-10-22, later).** The `d=2` plus line is now tabulated in the
same registry (rays `n=2l` floor 14 and `n=2l+1` floor 13); see
[class-a-d2-plus-rays-2026-10-22.md](class-a-d2-plus-rays-2026-10-22.md). The
non-claim above is superseded for that line only; the eight rays and their
receipts in this note are unchanged.

**Addendum (2026-10-23).** Gap four is now tabulated in the same registry,
both signs, four rays each; see [class-a-d4-rays-2026-10-23.md](class-a-d4-rays-2026-10-23.md).
`ALine.check_domain` now states the run-index note's full domain
(`q>=0`, `q+eps>=0`, `d<=2q+6eps+5`). The shared test surveys each line from
`q=0`. The eight rays above and their receipts are unchanged.
