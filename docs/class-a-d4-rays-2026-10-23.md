# Class A gap four: boundary hitting on (n+4,n,n+1) and (n+4,n,n-1), each on its whole domain (2026-10-23)

**Status:** repository-proved, computer-assisted, scoped to two
determinant-two class-A lines: `(n+4,n,n+1)` for every `n>=0` and
`(n+4,n,n-1)` for every `n>=3`. Each range is the line's whole PIP domain.
Independent human review is pending. On each line, every vertex of the
complete canonical swap-seed overlap graph has an offset-zero descendant.
Gaps `d>=5`, the class-C residual, universal #139/#84, G1 and PSC remain open.
No ledger claim is promoted; the status is that of the executable certificate.

## Stop/go

The literature decision of [p1b-class-a-run-index-2026-10-21.md](p1b-class-a-run-index-2026-10-21.md)
(Akiyama–Lee, Minervino–Thuswaldner, Barge) covers all of determinant-two
class A, and nothing is imported. The method is the residue-ray certificate of
[class-a-residue-rays-2026-10-22.md](class-a-residue-rays-2026-10-22.md),
which is parametric in `(d, eps, r)` and already tabulates d=2,3. The side-notes
ledger has no prior d>=4 entry. A finite probe on both signs (plus n=1..55,
minus n=3..47) found every vertex hitting, and the label set on each ray
`n = 4l + r` an exact union of intervals affine in `l`. Decision: **proceed**
by tabulating the eight d=4 rays in the shared registry, with no new
certificate code.

## Work shown

### Assumptions and hypotheses

- **Lines.** `sigma(x)=x y^(n+4) x`, `sigma(c)=c y^n x`, `sigma(y)=x y^(n+eps) c`:
  class A with `q=n`, `p=n+4`, `d=4`.
- **Domain.** Run-index note: `q>=0`, `q+eps>=0`, `4<=2q+6eps+5`. That is
  `n>=0` for `eps=+1` and `n>=3` for `eps=-1`. `ALine.check_domain` now
  states exactly these three conditions; it previously required `n>=1` and
  only the last one. `ALine.member` enforces the domain itself and admits
  `n=0`.
- **Conventions.** Canonical swap seeds, zero-based proper-prefix occurrence
  indices, bottom-minus-top integral offsets, and equal-letter offset-zero
  coincidences terminal, as in the gap-one and residue-ray notes.
- **Geometry** with `h=1/(beta-1)` (the `d=4` rows of the residue-ray formulas):

  ```text
  eps=+1:  P = 1-(n+1)h-(n+4)h^2-4h^3,  L = (1+4h+4h^2, 1, 1+h),     n^3 P(n,1/n) = -2n^2-4n-4
  eps=-1:  P = 1-(n-1)h-(n+6)h^2-4h^3,  L = (1+6h+4h^2, 1+2h, 1+h),  n^3 P(n,1/n) = -6n-4
  ```

  Both values are negative, so `h_n` lies in `(0, 1/n0]` for `n>=n0`.

### Derivation / reduction

Facts 1–3 of the residue-ray note apply verbatim with `d=4`:

1. **Scaling.** `4(al+b) = an + (4b - ar)` returns every Perron sign to the
   `A(h)+nB(h)` form.
2. **Child index.** `y' = 4k + ns + eps*y + Delta m`, so the realizable row
   indices are `[ceil(./4), floor(./4)]`. These are affine in `l`, because
   every y-run has `l`-slope 4.
3. **Monotonicity.** `T'` increases in `j` and in `y'`.

These give Theorem A (forward closure) and Theorem B (strict descent of an
`l`-affine potential) on each ray from its floor:

| line | ray | floor | rows | `|C|` | closure covered / gaps / windows | pieces / targets / descents | depth `<=` |
| --- | --- | ---: | ---: | --- | --- | --- | --- |
| `(n+4,n,n+1)` | `n=4l` | 24 | 86 | `40l+88` | 3,351 / 2,797 / 1,548 | 130 / 8 / 178 | `2l+9` |
| `(n+4,n,n+1)` | `n=4l+1` | 21 | 88 | `40l+90` | 3,383 / 2,835 / 1,584 | 126 / 8 / 159 | `2l+8` |
| `(n+4,n,n+1)` | `n=4l+2` | 22 | 78 | `40l+88` | 3,029 / 2,537 / 1,404 | 114 / 8 / 151 | `2l+11` |
| `(n+4,n,n+1)` | `n=4l+3` | 15 | 76 | `40l+92` | 2,931 / 2,453 / 1,368 | 112 / 8 / 144 | `2l+11` |
| `(n+4,n,n-1)` | `n=4l` | 24 | 93 | `40l+75` | 3,621 / 3,039 / 1,674 | 129 / 8 / 188 | `2l+9` |
| `(n+4,n,n-1)` | `n=4l+1` | 25 | 117 | `40l+145` | 4,539 / 3,817 / 2,106 | 157 / 8 / 212 | `2l+7` |
| `(n+4,n,n-1)` | `n=4l+2` | 22 | 109 | `40l+129` | 4,187 / 3,529 / 1,962 | 149 / 8 / 202 | `2l+7` |
| `(n+4,n,n-1)` | `n=4l+3` | 23 | 105 | `40l+125` | 4,001 / 3,377 / 1,890 | 139 / 8 / 190 | `2l+8` |

On every ray there are 9 real seeds in the carrier, 3 non-strict seed
candidates, 65 terminal splits and no conservative clip.

**Theorem (gap four).** For every `n>=0` on `(n+4,n,n+1)`, and every `n>=3`
on `(n+4,n,n-1)`, every vertex of the complete canonical swap-seed graph has
an offset-zero descendant.

*Proof.* For `n` at or above its ray's floor, Theorems A and B on that ray
apply. Below every floor, the exact complete graph has finite first-hit
depths and the cap is not reached. That covers `n=0..23` for the plus line
(`n=0` lies on no previously certified line: `p=2q+4` has `k=4`) and
`n=3..24` for the minus line. ∎

### Evidence and replay

From `kernel/`:

```sh
pixi run --locked mojo run -I . class_a_residue_ray.mojo certify 4 1 0 24     # likewise r=1..3, floors 21,22,15
pixi run --locked mojo run -I . class_a_residue_ray.mojo certify 4 -1 1 25    # minus floors 24,25,22,23
pixi run --locked mojo run -I . class_a_residue_ray.mojo survey 4 1 30
pixi run --locked mojo run -I . tests/test_class_a_residue_rays.mojo
```

From the repository root:

```sh
python oracles/python/class_a_carrier_closure.py 24 --ray 4,1,0               # one line per ray
python -m pytest -q tests/test_class_a_residue_rays.py
(cd evidence/class-a-d4-rays-2026-10-23 && sha256sum -c SHA256SUMS)
```

- **Tables.** `kernel/psc/class_a_ray_d4p.mojo` and
  `kernel/psc/class_a_ray_d4m.mojo`. They are generated, so each is a proof
  target. They are registered in `kernel/psc/class_a_ray_tables.mojo`.
- **Packet.** `evidence/class-a-d4-rays-2026-10-23/`.
- **Agreement.** The Mojo certificate and the independent Python verifier
  report identical closure and descent counts on all eight rays.
- **Regeneration.** The generator log regenerates both table files
  byte-identically from the exports.
- **Shared test.** `test_class_a_residue_rays` now surveys every line's domain
  below the floor from `q=0`.
- **CI.** The existing `class-a-residue-rays.yml` workflow iterates the
  registry.

### Negative controls

Per ray, the shared suite checks:
- A removed carrier row escapes closure.
- The other residue's carrier does not fit.
- A raised child potential, a mislabelled child `y'` and a missing descent
  row all refuse.

Domain refusals: minus members `n=0,1,2` refuse as outside the PIP domain.

Below the floors the certificate refuses rather than concluding:

| line | ray | refused at | reason |
| --- | --- | --- | --- |
| plus | `r=0` | 16, 20 | Sturm polynomial vanishing at the interval bound |
| plus | `r=1` | 17 | root inside `(0,q]` |
| plus | `r=2` | 18 | root inside `(0,q]` |
| minus | `r=1` | 21 | root inside `(0,q]` |

On the generator side:
- The carrier fit refuses from `n=8` on plus `r=0,1` and on minus `r=0,1,2`,
  because the run count or an endpoint is not yet affine.
- Descent generation refuses ("incomplete descent table") at the lower starts.
- Four rays (plus `r=2,3`, minus `r=0,1`) use the one-step slack fit on one
  row each.

These are fail-closed outcomes, not counterexamples.

### Non-claims / remaining gaps

- Only the two `d=4` lines. Gaps `d>=5` of class A are open: one line per
  `(d, eps)`, an infinite family that needs a certificate uniform in `d`.
  The class-C residual `d>=4`, aligned #138, universal #139/#84, G1 and PSC
  are also open.
- The cardinality formulas, the observed first-hit depths (at most 12 on the
  plus line and 10 on the minus line over the exported ranges) and the
  affine-fit starting points are finite observations. The generator is not
  evidence.
- The finite replay budget of `certify_finite_line` and
  `descent_witnesses_line` rises from `n<=24` to `n<=48`, so the first two
  members of the floor-24/25 rays can be replayed. This is a budget change,
  not a mathematical one.
- Not Lean-formalized; independent human review pending.
