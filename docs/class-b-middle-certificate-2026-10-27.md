# Class-B top layer: exact middle certificates and remaining finite gaps

**Status:** scoped, computer-assisted mathematical certificates; independent
Python exact arithmetic agrees with native Mojo. Independent human review is
pending. No governed claim or general PSC premise is promoted.

## Certified scope

Let `eps = ±1`, `q = g*l + r`, and
`(p,q,R_y) = (3q+6+6eps-g,q,q+eps)`. Assume the standing primitive irreducible
Pisot hypotheses and the canonical bottom-minus-top swap-seed convention.

The new uniform certificates prove that every vertex of the complete
canonical swap-seed graph has an offset-zero descendant in these domains:

| Sign | Gap | Residue | Quotient |
| --- | --- | --- | --- |
| plus | `g >= 16` | `2 <= r <= g-14` | every integer `l >= 4` |
| minus | `g >= 12` | `6 <= r <= g-6` | every integer `l >= 4` |

There are two 529-row carriers. For every non-target carrier label there is
an actual child decreasing `X=abs(k)+b`, with `0 <= b <= 3`. Thus its
first-hit depth is at most `abs(k)+3`. This is existential descent along
selected children, not decrease along every edge. Offset zero and equal-letter
coincidence remain separate targets in the downstream dictionary.

The remaining finite gaps from #363 are handled independently by the existing
ray certificate: plus `g=11..15`, minus `g=8..11`, **103 new rays**. Combined
with the preceding 83 rays, this gives 186 rays, plus gaps through 15 and
minus gaps through 11, each over its whole PIP domain after exact checks below
its certified floor. The new fitted floors are raised by `2g`; the maximum
certified floor is 88 and the maximum differential replay parameter is 103.
The final native/oracle replay logs are in the accompanying packet.

## Derivation

Write an integral offset as `(k,c,y)`, and use the invertible integer
coordinates `u=3k+c+y`, `d=c-3k`. The closed-form lengths and displacement are

```text
Lx = 3 beta^2 + (3+3eps-g) beta + 3eps
Lc = (beta+1)(beta-eps), Ly = beta(beta+1)
T = (beta+1)(u beta-eps*d) - g beta*k.
```

Put `h=1/beta`, `v=g*h`, and normalize lengths and displacement by `h^2`.
The characteristic equation is equivalent to

```text
q*h*(1+h) = E
E = 1-(3+eps)h-(4+3eps)h^2-2eps*h^3+v*h.
```

The three normalized length identities `h*(L M)_j-L_j=0` are checked
coefficient by coefficient after eliminating `q*h*(1+h)`. Both native and
independent verifiers derive the same integer polynomials.

For `k=a*l+b`, the normalized displacement becomes

```text
(u-eps*d*h)(1+h) - b*v - a*q*h + a*r*h.
```

Every margin is affine in `r*h`. Check both residue endpoints, `j0*h` and
`v-j1*h`, then clear the positive denominator `h*(1+h)`. Since `beta>q`,
`0<v<1/4` and `0<h/v<=1/g0`. To justify `beta>q`, the characteristic
polynomial at `q` is
`-(4+eps)q^2+(g-4-3eps)q-2eps < 0` for `q>=4g`, `g>=12`; its monic
positive tail has a root above `q`, bounded above by the Perron root.
The required member hull is

```text
E - (4v+j0*h)(1+h) >= 0,
```

because `q>=4g+j0`. Exact rational Bernstein coefficients after
`h=v*t`, with subdivision and strict checks on every included cell face,
certify the margins. An undecided cell refuses. The independent Python
implementation re-expands the power polynomial on each rational rectangle;
it does not reuse the native de Casteljau subdivision implementation.

### Carrier, core and seeds

The strict core has `abs(u)<=3`, `abs(d)<=6`, `abs(k)<=2`. Uniform sign checks
classify all 4,095 candidate typed labels: 1,875 strict labels on plus and
1,851 on minus. Every strict core label is in the corresponding proposed
carrier, and every carrier row endpoint is strict. Displacement is monotone
in `k`, so the whole integer row is strict. Every canonical swap seed is
within the core bounds. This is a containment proof, not a fit argument.

The exact finite core exports reproduce the 529-row tails on 15 rays per
sign. Five samples per ray use `l=4..8`: `l=5,6` determine the tail and
`l=7,8` check it. **The exact closure at `l=4` need not equal the table.**
The universally verified table is a closed superset there. All 150 native
exports agree with independently reconstructed labels and first-hit depths.

### Complete child closure

Each image has FIRST, RUN and LAST segments. The difference of two integer
run intervals is the full difference interval, as proved in Lean's
`segment_difference`. With parent `k=k_lo+j`, children satisfy

```text
k' = u-k+dx, d'=-2u+dc-3dx
u' = (q+4+eps)u-g*k-eps*d+3dx+dc+(m_bottom-m_top).
```

The permissible `j` are ceilings/floors of a form
`A*l+B+(C+D*r)/g`. Exact affine inequalities at both residue endpoints and
the gap floor bound those quotients uniformly. **Outer** bounds enclose all
actual children for closure; **inner** bounds guarantee actual occurrences
for descent. They need not agree. A quotient that varies with residue is
never replaced by a guessed single value.

All nine segment pairs and child `u'=-5..5` are covered. The two outer window
signs exclude `abs(u')>=6`. Every gap outside the child carrier is proved
geometrically non-strict. Native and independent closure counts agree:
16,098 plus and 16,604 minus. Terminal coincidences are handled explicitly;
all offset-zero labels terminate the descent argument.

### Descent and the minus corner

The finite exact synthesis proposes one `b(top,bottom,u,d,sign(k))` table per
sign. The symbolic certificate, not that synthesis, proves descent on every
piece of every carrier row, for unbounded `g,l` in the stated regime. It
covers each piece by guaranteed-realizable child intervals and checks
`X_parent-X_child-1>=0` at both endpoints for every `l>=4`.

| Domain | Pieces | Target pieces | Descent intervals | Candidate intervals | Maximum b |
| --- | ---: | ---: | ---: | ---: | ---: |
| plus `g>=16` | 1141 | 9 | 1468 | 4544 | 3 |
| minus `g>=13` | 1153 | 9 | 1456 | 4464 | 3 |

The common occurrence fails at minus `g=12` on row zero
`(x,x,u=-3,d=-6,k=-2)`: a selected RUN/LAST occurrence needs top run position
`m=g-13`. The exact missing inequality is `g-13>=0`, false at 12. That
refusal is preserved. The only middle residue at `g=12` is `r=6`; the existing
ray engine certifies the same carrier and potential for **every** `q=12l+6`,
`l>=4` (floor 54). Its independent counts agree, including 1,456 descent
intervals. This supplies the corner, rather than weakening occurrence legality.

Lean proves the generic natural-rank-to-target implication, the integer
segment-difference realization, and the proposed residue partitions. Those
are universally quantified interface theorems. The 529-row Bernstein/closure/
descent certificates are computer-assisted and are **not** Lean-formalized.

## Negative controls and remaining obligations

The packet preserves the first failed coarse hull `q>=4g`, its source, and an
exact rational point admitted by that hull where the required lower margin is
positive. Strengthening to `q>=4g+j0` removes that false parameter point.
This is a counterexample to the coarse relaxation, not to the substitution.
Removed carrier rows and zero potentials refuse; existing ray tests also
reject lowered/missing potentials, wrong rays and sub-floor certificates.
The segment iterator is compared with complete ordered occurrence support,
including an empty y-run and malformed image/cap refusals.

**The middle table does not extend to the boundary residues.** Exact strict
escaping children are recorded in `negative-controls/middle-outside-regime.json`:

| Sign, parameters | Parent `(top,bottom,k,c,y)` | Actual indices `(i,j)` | Missing child |
| --- | --- | --- | --- |
| plus `g=16,l=6,r=1,q=97` | `(x,y,6,20,-38)` | `(0,99)` | `(x,x,-6,-17,36)` |
| minus `g=13,l=6,r=5,q=83` | `(x,y,6,14,-32)` | `(0,83)` | `(x,x,-6,-17,36)` |

The missing child's coordinates are `u=1,d=1,k=-6`. Boundary carriers must
include that actual child and support a rank for it; extending the middle
certificate without changing the carrier is invalid. The low/high bands are
still plus `r=0,1` and `r=g-13..g-1`, and minus `r=0..5` and `r=g-5..g-1`.
The strip `l<4` for unbounded gaps is also untreated. These are separate from
the finite gaps now certified. No universal BH, A1′, G1, #84 or PSC conclusion
is asserted, and no class-A result is used to discharge a class-B obligation.

## Reproduction

From the repository root, after installing the locked kernel environment:

```bash
(cd kernel && pixi run --locked mojo run -I . tests/test_class_b_core_exact.mojo)
(cd kernel && pixi run --locked mojo run -I . tests/test_class_b_middle_certificate.mojo)
(cd kernel && pixi run --locked mojo run -I . tests/test_class_b_ray_certificate.mojo)
python oracles/python/class_b_middle_tables.py --check
python oracles/python/class_b_middle_potentials.py --check
python oracles/python/class_b_middle_geometry.py
python oracles/python/class_b_middle_closure.py
python oracles/python/class_b_middle_descent.py
python oracles/python/class_b_core_exact.py --packet evidence/class-b-step2c-2026-10-27/core-labels
python -m pytest -q tests/test_class_b_ray_certificate.py tests/test_class_b_step2c.py
(cd evidence/class-b-step2c-2026-10-27 && sha256sum -c SHA256SUMS)
sha256sum -c evidence/class-b-step2c-2026-10-27/SOURCE_SHA256SUMS
```

`kernel/class_b_core_exact.mojo` exports an individual bounded exact core
closure. `class_b_ray_replay.py` parallelizes canonical `one I` replays and
independent symbolic verification, retaining ray-index order and refusing on
any job failure or count discrepancy. Its output directory is never silently
overwritten. The dedicated workflow expects 186 rays; it repairs the inherited
83-versus-21 count assertion. The below-floor driver no longer inherits the
exploratory profile's unrelated `QMAX=48` guard.

Local compilation uses the lock-pinned Mojo version. Following an automatic
review rejection of a potentially networked compiler run, subsequent compiler
and replay execution used `tools/run_without_network.py`: inherited file
descriptors are closed, and an inherited seccomp filter denies networking.
Its self-test verifies denial before exec. The runtime restriction changes no
mathematical predicate. The benchmark records matching generic and segmented
labels on two members, with roughly ninefold lower elapsed time under the
recorded concurrent load; that is not a controlled throughput claim.
