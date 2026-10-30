# Class C: exact domain and lower-onset partitions (2026-10-29)

Status: exact algebraic domain lemma and computer-assisted canonical
swap-seed boundary-hitting certificates, conditional on the explicitly
listed implementation trust. No PDS, G1 or PSC conclusion. No governed claim
is promoted. Depends on PR #384, source
`53dd9547cea65d3cdb1fa80c4e16f97b712aabd4`.

The [stop/go](class-c-lower-strip-stopgo-2026-10-29.md) records the primary-source
check before implementation. All offsets are bottom minus top; alphabet order
is x,c,y. Offset zero is the target even when the two types differ; typed
y/y coincidence is not silently substituted for that target.

## 1. Exact Pisot domain, independent of symbolic closure

**Domain lemma.** In the class-C normal form, for every integer d>=6,
PIP holds exactly when n>=2d-5 on plus or n>=2d+1 on minus.
Normal form requires n>=0 and n-d+eps>=0. The lower endpoints were only
observed in #374/#384; this lemma establishes them uniformly.

For p=n+d, q=n, r=n-d+eps, the incidence matrix is
M=[[2,1,0],[0,1,2],[p,q,r]]. Direct determinant expansion gives

    chi(t)=t^3-(n-d+eps+3)t^2+(n-3d+3eps+2)t-2eps,
    chi(1)=-2d,
    chi(-1)=-2(n-2d+3eps+3),
    chi(2)=-2(n+d),
    chi(-2)=10d-6n-12eps-24.

At the stated starts p,q,r are positive (r>=2 even at d=6 on plus),
M^2 has all entries positive, and det M=2eps. Primitivity follows.
The four displayed evaluations are strictly negative on the domain;
for chi(-2) the upper bounds are -2d-6 (plus) and -2d-18 (minus).
The only possible rational roots of this monic integral cubic are ±1,±2;
all are excluded, so it is irreducible.

Let beta be its Perron root. Since chi(2)<0 and the polynomial is monic,
a root exceeds 2, hence beta>2. Write
chi(t)=(t-beta)(t^2+u t+v), where v=2eps/beta. Then |v|<1 and

    1+u+v = chi(1)/(1-beta) > 0,
    1-u+v = chi(-1)/(-1-beta) > 0.

These are precisely the algebraic quadratic Schur/Jury inequalities
|v|<1, |u|<1+v. Both remaining roots are strictly inside the unit disc.
This proves sufficiency without assuming Pisot or invoking the cone screen.
Conversely, for a PIP member the quadratic factor has both roots inside
that disc, so its value at -1 is positive and chi(-1)<0. This forces
n>2d-3eps-3, exactly the stated integer starts. One below the start
has chi(-1)=0; two below has chi(-1)=2. These are exact negative controls,
not numerical screening observations.

`domain_identities` derives chi from the symbolic matrix, compares all four
identities as exact polynomials, and certifies their signs on d=6+u,
n=2d+c+v, u,v>=0. It checks algebraic premises of this proof; it is not a
machine-checked Lean proof of the quadratic criterion. The boundary routine
checks the two excluded parameter lines as polynomial identities.

## 2. Parameter partitions and scope

A diagonal n=4d+c uses the existing T_C Piece(DIAGONAL), with its own label
set computed afresh. The upper four residual diagonals are c=-4,-3,-2,-1
(plus) and c=0,1,2,3 (minus). The proposed split is symbolic d>=12 plus
exact members 6<=d<=11. No equality of label sets between diagonals or small
members is assumed or required.

A middle cone is parametrized by nonnegative integers u,v:

    d=a+b+u+v,     n=4a+3b+4u+3v.

Its inverse is u=n-3d-a, v=4d-b-n. Therefore this is exactly
3d+a<=n<=4d-b, with no omitted congruence class (determinant -1).
The run lengths p,q,r are integral affine polynomials. Candidate a=b=16
has d>=32; it is strictly inside both residual strips. The driver
certifies PIP, symbolic closure and hitting before checking constancy for
row export. A label set is an output, never a premise.

A fixed gap line inside the residual strip is a *finite* interval, not an
unbounded ray. The `gap` driver enumerates precisely the interval from the
proved domain start through the integer immediately below T_C. At d=6 this
is 17 plus members and 15 minus members, all checked by the exact kernel.

**Certified results.** Both middle cones certify: 280 labels (plus), 250
(minus); all vertices reach offset zero. The maximum Pólya multiplier used
is zero: all shifted signs certify directly by coefficients. All eight
upper diagonals certify for d>=12, and all 48 exact end members d=6..11
certify independently. Hence the entire upper four layers have BH for
**every d>=6**, with no requirement that neighboring layers share labels.

| sign | n-4d | labels on every d>=12 |
|---|---:|---:|
| plus | -4 | 180 |
| plus | -3 | 228 |
| plus | -2 | 204 |
| plus | -1 | 198 |
| minus | 0 | 212 |
| minus | 1 | 238 |
| minus | 2 | 222 |
| minus | 3 | 216 |

The full gap-6 residual strip also certifies by 32 exact graphs. In particular
its plus start n=7 has 2,432 labels, against only 196 at the tail: the uniform
frozen-tail table cannot be reused at that edge.

After combining these results with T_C, the residual domain is d>=7,
2d-5<=n<=4d-5 (plus) or 2d+1<=n<=4d-1 (minus), excluding the proved
middle cone. For d>=32 the remaining bands are 2d-5<=n<=3d+15 and
4d-15<=n<=4d-5 on plus; 2d+1<=n<=3d+15 and 4d-15<=n<=4d-1 on minus.
For 7<=d<=31 the middle cone is empty. These are coverage deductions,
not claims about unknown graph sizes in those bands.

Final acceptance results and refusals are listed in the evidence packet.
The universal boundary-hitting statements apply only to pieces with
successful native certificates. Finite samples of any other proposed piece
remain experimental.

## 3. Soundness audit of the cone assumptions

This is a source/math audit, not independent human review or formal
verification of the engine. `psc.symbolic_cone` is unchanged.

- **Integral parameters and runs.** Region certifies a shifted closed orthant.
  The callers here supply integral affine run lengths, positive throughout.
  General rational-polynomial Cone inputs would need their own integrality
  argument. M^2 positivity is available directly for these families.
- **Region signs.** Shifting to u,v>=0, nonnegative coefficients with positive
  constant term imply strict positivity even on the boundary. Multiplication
  by (1+u+v)^k preserves sign; k<=24 is an incompleteness budget, not a
  positivity assumption. Sample signs select a proposal only.
- **Root identification.** The domain lemma independently supplies the unique
  root beta>2. The fixed-point proposals x0=r+2 and
  g(x)=r+2(q+p/(x-2))/(x-1) all exceed 2 here: r>=2 and x>2 imply g(x)>r.
  The implementation checks positive bracket denominators and chi(L)<0<chi(U),
  so these proposals bracket that unique root. No reliance on iteration
  convergence or a presumed Pisot condition is needed. Generic callers
  without a unique-root argument must audit root identification separately.
- **Signs at beta.** Monic reduction gives degree <=2 exactly. A positive
  denominator squared preserves endpoint signs. Equal nonzero endpoint
  signs plus monotonicity, or curvature away from zero, imply the same sign
  throughout the bracket. An undecided endpoint or derivative refuses.
- **Fitted run bounds.** Three samples propose integral affine bounds only;
  the bound and its adjacent integer are checked uniformly. Positive run
  length and positive tile length give monotonicity. Empty/clipped blocks
  are tested at legal endpoints before fitting. A growing interval or cap
  refuses; it is not rounded into a finite graph.
- **Graph identities.** Offsets use exact Q[s1,s2] vectors; zero-offset
  reachability is reverse finite-graph search. In general two symbolic labels
  could specialize to one; the extra constant-integer-offset check here
  prevents such parameter-dependent collisions. All children are certified
  before a vertex is processed, and typed zero vertices are terminal by the
  same convention as the exact graph. S′ then applies at every member.
- **Cross-check scope.** The existing sample comparison checks labels, not
  edge equality. Our independent literal-word/Fraction oracle also checks
  all-vertex hitting at its finite samples; it cannot validate a universal
  region by sampling. The symbolic sign/closure implementation remains a
  trusted input, as do finite_exact, qpoly and the exact-member kernel.

## 4. Reproduction of T_C and independent finite checks

Both complete T_C theorem runs and its native test were independently rerun
from the pinned source; all three outputs match the earlier packet byte for
byte. Their archived replay logs retain every sign refusal before successful
partitioning. The separate exact oracle reproduces the 196/214 tail sets
and 198/216 adjacent controls. Thus the larger lower-strip sets are not an
artifact of assuming the frozen table.

All 122 independent graph checks pass, including all 48 top end members and
32 gap-6 members, four members per symbolic diagonal, four per middle cone,
and two old tail members. The separate exact Routh/irreducibility grid has
13,432 decided agreements and 20 explicit refusals (all outside the domain).
The implementation audit above identifies assumptions and preserves the
engine trust; sampling is not treated as proof of universal closure.

## 5. Replay, provenance and non-claims

The evidence README gives all commands, code hashes, exact dependency commit,
certificate logs, oracle receipts, refusals and SHA256SUMS. The dedicated
workflow builds Mojo once and replays the accepted pieces and controls.
Neither the trusted engine nor vendored arithmetic is edited.

No whole residual-strip proof, spectral consequence, all-overlap realization
transfer, or completion-ledger discharge is asserted. The lower Pisot edge
may have graph size growing with d, beyond the constant-label method.
Independent human review of the full argument and implementation remains
pending. Existing governed claim statuses are unchanged.
