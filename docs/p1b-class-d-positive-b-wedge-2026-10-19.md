# Class-D positive-b residual: exact wedge test — 2026-10-19

**Status:** active proof attempt for issue #139. The pull request for this
work is governed by the repository's enforced show-your-work policy:
assumptions, derivation, replay evidence, negative controls, and non-claims are
all explicit in the PR body and must remain so as the proof evolves. This note introduces no theorem
until the exact two-parameter closure runs succeed. It reuses the already
audited Theorem W engine rather than adding a new quotient or sampled census.

## 1. Exact residual domains

The complete class-D residual parameterization is

```text
s = +1: p = 3 + 3a + b, q = 2 + 3a + b, r = 2a + b
s = -1: p = 5 + 3a + b, q = 6 + 3a + b, r = 4 + 2a + b
a >= 0, b >= 0.
```

Merged PR #277 certifies both infinite boundary lines `b=0`. The remaining
domains are exactly `b>=1`.

Put `c=b-1>=0`. Then the two open interiors are single affine wedges:

```text
s = +1:
(p,q,r) = (4,3,1) + a(3,3,2) + c(1,1,1)

s = -1:
(p,q,r) = (6,7,5) + a(3,3,2) + c(1,1,1).
```

The directions in `(q,r)` are again `(3,2)` and `(1,1)`, determinant
one, so every integer point of each positive-b residual appears exactly once.

## 2. Why this is the highest-value test

`psc.symbolic_line.ClassWedge` already proves complete two-parameter
seed-overlap closure on an affine quadrant when:

1. the PIP property is certified uniformly;
2. every sign at the Perron root is certified by the nonvanishing-norm /
   quadrant machinery;
3. the symbolic seed graph closes completely;
4. every symbolic vertex reaches offset zero;
5. the symbolic graph agrees with exact graphs at two interior points.

This is exactly the #139 target on this scoped class. No projected-vector
lifting gap is introduced: the engine constructs the actual seed-patch overlap
graph and its complete child relation.

## 3. Exact test

The dedicated workflow runs:

```sh
cd kernel
pixi run mojo run -I . symbolic_line_certificate.mojo wedge D 4 3 1 3 3 1 1 2 1
pixi run mojo run -I . symbolic_line_certificate.mojo wedge D 6 3 1 7 3 1 5 2 1
```

A successful job must report a complete symbolic graph in a certified quadrant
and exact graph equality at the engine's two cross-check points. A failure is
also useful evidence: it names the first uncaptured sign, changing graph, run
bound or state-cap obstruction. No failure is to be interpreted as a
counterexample to boundary hitting unless the exact mathematical predicate
itself is falsified.

## 4. Complete-quadrant certificate

`kernel/class_d_positive_b_certificate.mojo` now composes the existing exact
proof objects instead of stopping at the wedge core:

1. `certify_wedge` proves BH on one eventual quadrant
   `a>=a0, c>=c0`;
2. `wedge_edges` enumerates every parameter line covering the complement;
3. `certify(line)` proves each such line, including its exact finite prefix.

Therefore a successful driver run covers **every integer point** of both
positive-`b` residual quadrants. It prints
`COMPLETE_POSITIVE_B_WEDGE` only after every core and boundary-line proof has
completed without refusal.

This still remains scoped class-D closure, not universal #139.

## 5. Acceptance after a successful run

Success of a wedge core alone is not yet the whole quadrant if the engine moves
its certified corner to `a>=a0, c>=c0`. The finite strips outside that core
must then be certified by the engine's exact boundary-line mechanism, exactly
as in Theorem W. The result can be promoted only after those strips are pinned
and replayed.

If both wedges and all required strips certify, class-D boundary hitting is
closed completely by combining:

- Corollary W1 for `r>=q-1`;
- PR #277 for both `b=0` residual boundaries;
- the two positive-b wedge certificates here.

That would close #139 on all determinant-two class D, not universal #139.

## 6. Firewalls

- no uniform contraction margin is assumed;
- no unimodularity is introduced;
- no projected path substitutes for an occurrence-labelled overlap path;
- the failed literal transport of the sealed `b=0` spine is not reused;
- no finite sample is a theorem;
- a capped/undecided exact run refuses promotion.

## 7. Rank-one b-direction and the occurrence compensation law

The positive-b direction adds one extra `y` to **every** image. In letter
order `(x,c,y)` the incidence matrix therefore has the exact form

```text
M(a,b) = M(a,0) + b e_y 1^T.
```

For an overlap offset vector `w` this gives

```text
M(a,b) w = M(a,0) w + b (1^T w) e_y.
```

Hence an occurrence-labelled child

```text
w' = M(a,b)w + prefix_bottom - prefix_top
```

can retain a b-independent target only if the selected prefix difference
absorbs the term

```text
-b (1^T w) e_y.
```

This is the exact compensation law. It explains the PR #277 negative control:
the sealed boundary row `(c,y,-2,4,-3)` has `1^T w=-1` and keeps FIRST/FIRST
prefixes, so it supplies no compensating `+b e_y` and the edge moves.

A successful two-parameter certificate therefore has only two legitimate
forms:

1. let the symbolic child state itself depend affinely on b; or
2. choose occurrence indices whose y-prefix difference changes by exactly
   `-b(1^T w)`.

No new quotient is needed. The existing ClassWedge engine already allows
affine state coordinates and affine run positions, so the candidate workflow
is testing precisely whether this compensation closes on a finite symbolic
family.

If the wedge engine fails, its first uncaptured run-position/sign decision
should be interpreted against this law before introducing any additional
state coordinate.

## 8. Positive-b rank-spine transport theorem (minus branch)

The sealed minus `b=0` spine has 145 labels, six rank-zero targets and 139
selected strict-rank descents.  Write `w=(w_x,w_c,w_y)` and
`s(w)=w_x+w_c+w_y`.  Exhaustion of the sealed rows gives

```text
s(w) in {-1,0,+1}
for every one of the 145 labels.
```

Adding one unit of the residual parameter `b` adds one `y` to every
substitution image, hence

```text
M(a,b) = M(a,0) + b e_y 1^T.
```

An occurrence inside a `y` run may be transported in exactly two uniform
ways: keep its distance from the run start (b-coefficient 0) or keep its
distance from the run end (b-coefficient 1). First occurrences have coefficient
0 and last occurrences coefficient 1. Therefore the old child is preserved
whenever

```text
n_bottom - n_top = -s(w).
```

This directly transports 129 selected spine edges.

Four further rows use a different edge already present in the complete
`b=0` support:

```text
row 49  -> 116: top 2a+5,       bottom 2a+5+b
row 70  -> 102: top a+2+b,      bottom 0
row 96  ->  65: top 0,          bottom a+2+b
row 117 ->  50: top 2a+5+b,     bottom 2a+5.
```

Each target has strictly smaller sealed rank.

The remaining six rows are `y/y` states and admit explicit positive-`b`
descents:

```text
122 -> 69: top 0,              bottom b
142 -> 97: top b,              bottom 0

129 -> 71: top 2a+5+b,         bottom b
135 -> 95: top b,              bottom 2a+5+b

123, b=1 -> 45: top 2a+6,      bottom 0
123, b>=2 -> 71: top 2a+5+b,   bottom b-1

141, b=1 -> 34: top 0,         bottom 2a+6
141, b>=2 -> 95: top b-1,      bottom 2a+5+b.
```

The target ranks are respectively below the source ranks.  The exact integer
regression
`tests/test_class_d_positive_b_spine_transport.py` evaluates the child
formula from the actual words and verifies the 129/4/6 partition and every
displayed strict descent.

**Proposition (scoped rank descent).** For every integer `a>=2,b>=1`, every
non-target label of the sealed 145-row minus spine has an explicit
occurrence-labelled child in the same label set of strictly smaller sealed
rank.

This proposition is **not yet the minus-quadrant BH theorem**.  The remaining
logical obligation is **positive-b cover closure**: every seed-reachable child
must remain in the 145-label upper cover (or in a proved enlarged finite
cover).  The complete ClassWedge driver in §4 attacks exactly that obligation.
Once cover closure is proved, the displayed rank is a terminating BH
certificate of depth at most four.

## 9. Class-D Perron-gap monotonicity on both residual signs

There is a shared analytic reason the positive-`b` support tends to shrink.

Put

```text
D = a+2 >= 2,
q = r+D,
p = q+s,      s in {-1,+1},
r = 2D-2s-2+b,
beta = r+d.
```

Thus `d=beta-r` and, after normalizing `ell_y=1`,

```text
ell_c = d/2,
ell_x = d/2 + s/beta,
```

because `p-q=s`.

### Lemma

For fixed integer `D>=2` and either residual sign `s=±1`:

```text
d > 2,
d is strictly decreasing in b,
and d -> 2 as b -> infinity.
```

### Proof

The characteristic polynomial is

```text
chi(X)=X(X-2)(X-r)-2(r+D)(X-1)-2(r+D+s).
```

First,

```text
chi(r+2) = -2(Dr+2D+s) < 0,
```

throughout the residual positive-`b` region. Since `chi(X)->+infinity`
and the PIP root `beta` is the unique real root above one,
`beta>r+2`, hence `d>2`.

For the derivative we need the stronger inequality
`beta(d-2)>D`. Set

```text
x0 = r+2 + D/(r+2).
```

Direct simplification gives

```text
chi(x0)
 = [D^3 - D(r+2)^4 - 2s(r+2)^3] / (r+2)^3.
```

On both positive-`b` residuals `r+2>D`. For `s=+1` the numerator is
immediately negative. For `s=-1` it is
`D^3-(r+2)^3(D(r+2)-2)`, also negative because
`r+2>D` and `D(r+2)-2>1`. Therefore `beta>x0`, hence

```text
d-2 > D/(r+2) > D/beta,
```

so `beta(d-2)>D`.

Regard the root equation as `F(r,d)=chi_r(r+d)=0` with `D,s` fixed.
In both signs,

```text
partial_r F = 2(beta(d-2)-D) > 0,
partial_d F = chi'(beta) > 0.
```

The second inequality holds because the Perron root is simple and larger than
the other two roots. Thus

```text
dd/dr = -(partial_r F)/(partial_d F) < 0.
```

Since `r` increases with slope one in `b`, `dd/db<0`.

Finally `d>2` and monotonicity give a limit `L>=2`. In the exact root
equation the coefficient of `r^2` is `d-2`; if `L>2`, that positive
quadratic term cannot be cancelled as `r->infinity`. Hence `L=2`.
QED.

### Consequence for the closure proof

Both residual signs approach a common unit-scale limit while retaining the
same rank-one `b` update. This does **not** by itself prove support inclusion:
the `s/beta` correction in `ell_x` and each offset inequality must still be
checked together. It does prove that no new proof should depend on a fixed
positive contraction margin, and it explains why the exact positive-`b`
graphs observed so far shed boundary labels and approach smaller stable cores.

The uniform support theorem still requires exact sign control; the complete
ClassWedge certificate and the independent exact Q(beta) oracle remain the
authoritative routes.

## 10. Execution audit: the current candidates refuse

The audit of PR #283 at `b28ed5f` (with the diagnostic/copy repairs in this
revision) ran the canonical Mojo programs using the available **Mojo 1.1.0
(8189361e)** release compiler. This is supplemental execution, not a receipt
from the pinned `1.1.0.dev2026090805` compiler: `pixi install --locked` failed
while fetching a conda-forge dependency, and direct retrieval of the pinned
compiler timed out. The observed GitHub Actions runs were queued. Reproduction
commands, source digests and verbatim refusal logs are under
`evidence/class-d-positive-b-audit-2026-10-19/`.

**Neither complete quadrant certified. No boundary strip was reached.**
The complete driver now accepts `plus`, `minus`, or `both` (default), and CI
runs the two signs independently, so the first plus refusal cannot hide the
minus result. The sealed-cover drivers needed explicit `SymVertex.copy()`
calls to compile; those repairs do not alter the proposed covers.

### First exact obstructions

Here `c=b-1` is the second ClassWedge coordinate; letters are `(x,c,y)` in
the offset labels (the letter `c` is distinct from the parameter `c`).

| Program | First source | Refusal |
| --- | --- | --- |
| Complete plus | `(x,x,0,1,0)` | Strict least-run bound at `(a,c)=(200,200),(400,200),(200,400)` is `-808,-1408,-1007`; the second-coordinate difference is `-199`, not divisible by the sample step `200`. |
| Complete minus | `(c,c,-1,0,0)` | Nonstrict least-run bound at `(200,200),(400,200)` is `811,1412`; the difference is `601`, not divisible by `200`. |
| Minus sealed cover | row 1, `(x,c,-1,3,-2)` | Realness reader cannot certify `c^2+3ac-2a^2-35a-62` on a shifted quadrant. |
| Plus sealed cover | row 0, `(x,x,-5,8,-4)` | Realness reader cannot certify `2c^2+(6a+34)c-4a^2+70a+126` on a shifted quadrant. |

Both first fitted bounds come from empty occurrence blocks, before the
engine intersects with the legal run range. For the plus source `(x,x,e_c)`,
top FIRST / bottom RUN has child translation
`beta*ell_c+ell_x+k*ell_y>ell_x` for `k>=0`, so it is never real. For the
minus source `(c,c,-e_x)`, top RUN / bottom FIRST has translation
`-beta*ell_x-ell_c-k*ell_y<-ell_c`, also never real. Clipping or rejecting
these empty blocks **before fitting** is therefore a justified correction,
with no cover enlargement and no change to the mathematical child relation.
It does not resolve the later sign-reader and changing-support obstructions.

The last two polynomials change sign arbitrarily far out: along `c=a` their
leading coefficient in `a` is positive; along `c=a/2` it is negative (take
even integer `a`). A larger corner or cap cannot give either polynomial a
constant sign. These are **auxiliary sign-reader obstructions**, not escaped
children, nor a counterexample to BH. In particular, the minus reader has not
even finished registering the cover, and neither checker reaches its
all-child inclusion test.

This distinction can be checked directly. The characteristic polynomial
simplifies to

```text
chi(X) = X^3-(r+2)X^2-2DX-2s,
beta(d-2) = 2D + 2s/beta,     d=beta-r, D=a+2.
```

For the minus row, normalizing `ell_y=1` gives
`t=d-2+1/beta`. Its realness margins are
`3d/2-2+1/beta>0` and
`2-d/2-2/beta = 1-(D+2)/beta+1/beta^2>0`, since
`beta>r+2=2D+b+2>D+2`. Thus this row really is an overlap on the whole
minus positive-b family despite the auxiliary polynomial's sign change.
For plus row 0, `t=3d/2-4-5/beta`; its margins are
`2d-4-4/beta=4(D-1)/beta+4/beta^2>0` and
`4-d+6/beta=2+(6-2D)/beta-2/beta^2>0`. The latter follows from
`beta>r+2>=2D-1>=3`. Again the failed auxiliary sign is not a failed
geometric inequality.

### A genuine obstruction to one fixed real subcover

The plus sealed row 12 is `(x,c,-5,11,-8)`. Its normalized realness margins
are

```text
lower = 7d/2-8-5/beta,
upper = 8-5d/2+6/beta.
```

Along `b=lambda*a` with fixed positive `lambda`, the preceding exact root
identity gives `d -> 2+2/(2+lambda)`: `beta>=r+2` first bounds `d`, then
`beta/a -> 2+lambda`. Along `b=a` the lower and upper margins both tend to
`4/3`, so the label is real for all sufficiently large `a`. Along `b=10a`
the lower margin tends to `-5/12`, so the label is not real. Both rays enter
every shifted quadrant. Therefore the plus checker cannot classify *every*
sealed label as uniformly real or uniformly non-real on a single eventual
quadrant. This concerns the proposed upper-cover strategy; it does not assert
that row 12 is seed-reachable at every parameter.

The new canonical regression
`kernel/tests/test_class_d_positive_b_obstructions.mojo` reproduces the exact
least-run sample values and the row-12 sign change at `(a,b)=(200,200)` and
`(200,2000)`. It declares a counter-calibration contract, not a BH claim.
The existing literal-spine negative control and 129/4/6 transport tests remain
in force; their regression suite, including the 56-member exact support grid,
passed in this audit.

### Correct next proof obligation

There is no observed cover escape to justify enlarging the 145 or 718 labels.
The next correction must address the representation of the decisions:

1. Clip occurrence ranges against the actual run endpoints before requiring
   affine geometric endpoints. `psc.symbolic_cone._ConeClosure.expand` already
   implements this exact strategy. A new specialization must preserve all
   old pinned verdicts, or explicitly account for changed certified corners.
2. Use Perron-root inequalities/brackets for genuinely uniform margins such
   as the two first sealed rows above. A changing conjugate norm or
   Sturm-sequence entry must not be mistaken for a changing Perron sign.
3. For genuinely changing support, certify parameter chambers (including
   their interface lines), or construct an upper relation whose **every
   actual child** is covered and whose selected descending occurrences are
   valid on their declared regions. A fixed selected graph alone is not enough.
4. Only after a core succeeds, certify every `a<a0` and `c<c0` line and its
   finite prefix. If the minus transported rank is used, its `a>=2` hypothesis
   must be included in the core and `a=0,1` handled separately.

This is a narrowed continuation of the existing parametric-overlap stop/go
in `p1b-catch-up-free-ppvc-2026-10-07.md` section 3 and the established
line/cone certificate contracts, not a new general PSC mechanism or a novelty
claim. The workflow now covers all kernel imports, both oracle layers, the
sealed evidence and tests, and uploads failure logs as well as success logs.
All certificate errors and missing completion receipts remain fatal.

**Status:** both positive-b quadrants remain open; no scoped class-D theorem,
ledger promotion, manuscript theorem update, #139 closure, or PSC conclusion
is warranted by these runs. Existing `b=0` and W1 results are unchanged.

Validation also reproduced the existing full symbolic-line Mojo regression,
including its pinned successful class-B/class-D lines and negative controls,
under the available release compiler. Generated ledger/math-catalogue checks,
vendoring pins, Markdown integrity, plus-carrier binding and transport tests
passed. The unchanged base also has separate governance blockers: a
`DensityToPDSBridge` status-anchor mismatch in `docs/proof-ladder.md:17`, stale
`proof/proof-bank.json`, and malformed/trailing manuscript content detected by
`check_manuscript_source.py` at line 1357. These were recorded, not silently
waived; full CI/Lean/TLA validation and merge acceptance are not claimed.

## 11. Post-audit repair: empty blocks and conditional descent geometry

The execution audit in §10 exposed two logically different failures.  They
must be repaired separately.

### 11.1 Empty occurrence blocks are clipped before fitting

The old `symbolic_line._Closure.expand` first fitted the unconstrained
geometric run interval and only afterward intersected it with the legal run
positions.  That is stronger than the mathematics requires and is wrong for
an empty legal block: an empty set has no boundary that needs an affine fit.

The repaired order now matches `symbolic_cone._ConeClosure.expand`.

For a run-position difference `m`, write

```text
lower(m) = ell_bottom + t + m ell_y,
upper(m) = t - ell_top + m ell_y.
```

The actual run interval is `m in [rlo,rhi]`.  Before any call to
`least_m`, the engine proves

```text
lower(rhi) <= 0  => block empty,
upper(rlo) >= 0  => block empty.
```

Only a surviving geometric boundary is fitted; if a legal run endpoint is
already inside the real interval, that endpoint is used directly.

This exactly disposes of the two first PR #283 refusals.

- Plus source `(x,x,e_c)`, FIRST/RUN: at the first legal run position
  `m=0`, the shift is `beta ell_c + ell_x > ell_x`, so
  `upper(0)>0`.  Every legal `m>=0` is still farther past the upper wall.
- Minus source `(c,c,-e_x)`, RUN/FIRST: the largest legal position is
  `m=0`, where the shift is `-beta ell_x-ell_c < -ell_c`, so
  `lower(0)<0`.  Every legal `m<=0` is still below the lower wall.

`kernel/tests/test_symbolic_line_empty_blocks.mojo` asks the same uniform
Perron-sign prover used by the certificate to verify these two endpoint
inequalities.  The old non-affine sample values remain pinned separately in
`test_class_d_positive_b_obstructions.mojo`; the repair does not erase the
negative calibration.

### 11.2 #287 is algebraic descent; geometry is conditional

The merged positive-`b` spine verifier proves valid child-index formulas and
the exact lower-rank child **state**.  It did not independently prove that the
selected target tiles overlap geometrically at every parameter.  The source
and contract wording are corrected accordingly.

For the minus residual this missing geometry can be proved without parameter
chambers.

Normalize `ell_y=1`, put

```text
d = beta-r,
u = 1/beta.
```

On the #287 domain `a>=2,b>=1`, set `D=a+2>=4`.  Exact evaluations of the
class-D cubic give

```text
chi(r+2) < 0,
chi(r+3) = 2Db + 6D + b^2 + 6b + 11 > 0,
chi(10) = -2(110D + 50b - 401) < 0.
```

The PIP root is the unique root above two, hence

```text
2 < d < 3,
0 < u < 1/10.
```

The Mojo geometry checker also certifies these three Perron comparisons on
the whole shifted ClassWedge region `a>=2,c=b-1>=0`; it refuses if its sign
proof shrinks that declared region.

Now put

```text
X = d-2,
Y = 10u.
```

Then `0<X<1`, `0<Y<1`, and twenty times every overlap-realness margin of a
fixed integral label is an integer-affine form in `X,Y`:

```text
20 ell_x = 20 + 10X - 2Y,
20 ell_c = 20 + 10X,
20 ell_y = 20.
```

For each selected #287 source/target pair, the exact checker assumes the
closed box

```text
0 <= X <= 1,
0 <= Y <= 1
```

and the two closed source-realness margins.  For each target margin `T`, it
then asks the checked rational Farkas kernel to refute

```text
T <= 2.
```

Thus the conclusion is stronger than interiority:

```text
source real  =>  each target physical margin > 2/20 = 1/10.
```

There are 141 source/branch cases because rows 123 and 141 have separate
`b=1` and `b>=2` targets, and therefore 282 checked margin implications.
The canonical code is
`kernel/psc/class_d_positive_b_geometry.mojo`; its driver prints
`CLASS_D_MINUS_POSITIVE_B_GEOMETRY_CERTIFIED`.

The exact dependency for the minus quadrant is consequently

```text
#287 valid child indices + exact lower-rank state
+ conditional target realness (>1/10 margins)
+ conditional carrier closure
=> BH in at most four rank steps.
```

Only the third line remains open.

### 11.3 Plus row 12 still requires chambers or a conditional cover

Nothing in the empty-block repair removes the genuine plus-support change.
For row 12 `(x,c,-5,11,-8)` the lower margin is

```text
L = 7d/2 - 8 - 5/beta
  = -1 + (7D-5)/beta + 7/beta^2.
```

Hence its zero condition at the Perron root is

```text
beta^2 - (7D-5) beta - 7 = 0.
```

Eliminating `beta` with the cubic gives the parameter resultant

```text
49 b^2 - 217 D b - 140 D^2 + 127 b + 262 D - 329 = 0.
```

This resultant is a useful algebraic superset of the possible sign-change
locus; it is **not** by itself asserted to be exactly the Perron chamber wall,
because a resultant may also vanish through a non-Perron conjugate.

The plus continuation must therefore do one of two things:

1. split the parameter domain by certified Perron-sign chambers and cover all
   chamber interfaces; or
2. prove a conditional upper relation that never needs a uniform
   real/non-real classification of row 12.

No cover enlargement is justified by the audit: no escaped actual child was
found.

## 12. Plus row-12 chamber collapses to six wedges and six lines

The first genuine plus-cover obstruction from §10 is row 12
`(x,c,-5,11,-8)`.  Put `D=a+2` and

```text
A = 7D-5,
g(X) = X^2 - A X - 7.
```

Its changing lower realness margin is positive exactly when `g(beta)<0`.
The positive root of `g` lies strictly between `A` and `A+1`, because

```text
g(A)   = -7,
g(A+1) = A-6 > 0.
```

Since `beta` is the unique cubic root above two, the two easy outer
comparisons are decided by `chi(A)` and `chi(A+1)`.  As functions of the
**original** positive-b parameter `b`, their zero thresholds are

```text
b0(D) =
 (245 D^3 - 511 D^2 + 345 D - 77) / (7D-5)^2,

b1(D) =
 (245 D^3 - 392 D^2 + 200 D - 34) / (7D-4)^2.
```

The location of these thresholds relative to the integer lattice is exact:

```text
b0-(5D-4)
 = (35D^2-60D+23)/(7D-5)^2 > 0,

(5D-3)-b0
 = 2(7D^2-5D+1)/(7D-5)^2 > 0,

b1-(5D-3)
 = (35D^2-48D+14)/(7D-4)^2 > 0,

(5D-2)-b1
 = 2(7D^2-4D+1)/(7D-4)^2 > 0.
```

Every numerator is positive for `D>=2`.  Therefore

```text
5D-4 < b0 < 5D-3 < b1 < 5D-2.
```

So on the **integer** parameter lattice the only possible middle value is

```text
b = 5D-3.
```

Recall the ClassWedge coordinate `c=b-1`; with `D=a+2` this becomes

```text
low outer region:  c <= 5a+5,
interface line:    c  = 5a+6,
high outer region: c >= 5a+7.
```

No nonlinear infinite chamber family is required.

### 12.1 Exact lattice decomposition

First cover the cone

```text
0 <= c <= 5a
```

by five adjacent unimodular wedges.  For `k=0,...,4` put

```text
(a,c) = u(1,k) + v(1,k+1),   u,v>=0.
```

The inverse is

```text
u = (k+1)a-c,
v = c-ka.
```

On the sector `ka <= c <= (k+1)a`, `u,v` are nonnegative integers, and
the determinant of consecutive directions is one.  Thus these five wedges
cover every lattice point with `0<=c<=5a`, with no missing residue classes.

Substitution runs on wedge `k` are

```text
p = 4 + (3+k)u + (4+k)v,
q = 3 + (3+k)u + (4+k)v,
r = 1 + (2+k)u + (3+k)v.
```

The remaining low/interface points are the six affine lines

```text
c = 5a+j,    j=1,...,6,
```

on which

```text
p = 8a + 4+j,
q = 8a + 3+j,
r = 7a + 1+j.
```

Finally the high region has the single unimodular parameterization

```text
(a,c) = (0,7) + u(1,5) + v(0,1),   u,v>=0,
```

hence

```text
p = 11 + 8u + v,
q = 10 + 8u + v,
r =  8 + 7u + v.
```

The determinant of `(1,5),(0,1)` is one, so this is again an exact lattice
cover.

Therefore the entire plus positive-b quadrant is the finite union of

```text
5 low two-parameter wedges
+ 6 affine lines
+ 1 high two-parameter wedge.
```

### 12.2 Candidate certificate

`kernel/class_d_plus_positive_b_chambers.mojo` certifies each of the six
wedges using the existing exact `certify_wedge` engine.  If a wedge core
moves to `u>=u0,v>=v0`, every omitted strip is enumerated by
`wedge_edges` and certified by the existing exact line engine, including
its finite prefix.  The six explicit chamber/interface lines are also run
through `certify` in norm mode.

Thus a successful
`CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED` receipt covers every integer
point of the plus positive-b residual, not merely an asymptotic chamber core.

`kernel/tests/test_class_d_plus_positive_b_chambers.mojo` independently
reconstructs the original residual substitution from the chamber inverse on a
large lattice grid.  That regression is a calibration; the universal lattice
coverage is the explicit inverse formulas above.

This chamber certificate remains a **candidate** until canonical execution
succeeds.  It does not change the status of class D, universal #139, #84 or
PSC.

