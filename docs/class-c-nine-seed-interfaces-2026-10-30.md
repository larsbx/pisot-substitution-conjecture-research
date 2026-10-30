# Class-C lower cone: all nine first-generation seed interfaces (2026-10-30)

**Status:** repository-proved by the scoped hand argument below; independent
human review pending. Executable checks are finite replays of that argument.
No forward-closed carrier, boundary hitting (BH), pure discrete spectrum,
G1 or general PSC conclusion is established here.

This extends [Theorem R_C](class-c-lower-cone-tile-ratio-walls-2026-10-30.md),
merged in PR #404 at d7bb85a9c96bf2ab526d3b41b5ce433a45256c4a.
The [targeted literature decision](class-c-nine-seed-stopgo-2026-10-30.md)
precedes the implementation. The specialization below is new repository work;
substituting overlaps and counting segment pairs are standard constructions.

## Work shown

### Assumptions and hypotheses

Integers d>=7, eps in {+1,-1}; p=n+d, r=n-d+eps, with

    sigma(x)=x y^p x, sigma(c)=c y^n x, sigma(y)=c y^r c;
    plus:  n=2d-5+c, 0<=c<=d+4;
    minus: n=2d+1+c, 0<=c<=d-2.

Here c in an integer expression is the parameter, distinct from the letter c.
Theorem P_C supplies the scoped primitive irreducible Pisot hypothesis.
Normalize ell_y=1, and put a=ell_x, b=ell_c, Delta=a-b, h=2b-a.
The established exact identities and inequalities are

    beta*a=2a+p, beta*b=a+b+n, beta=r+2b;
    Delta=d/(beta-1), h=1-eps/beta;
    1<b<a<4, r+2<beta<r+5, r>=3.

Use bottom-start minus top-start for a state's displacement. Strict interior
intersection of (u,v,w) means -ell_v<w<ell_u. No legality/realization bridge
from seed-patch states to every return-vector overlap is assumed. No tile-length
integer-independence hypothesis is used.

### Derivation / reduction

#### A necessary new mixed-length wall

The existing individual length and gap walls do not decide floor(a+b).
The following exact integer partition completes the first-layer interface:

| sign | parameter range | strict sum interval |
|---|---|---|
| plus | c=0 | 5<a+b<6 |
| plus | 1<=c<=ceil(d/2) | 4<a+b<5 |
| plus | ceil(d/2)+1<=c<=d+4 | 3<a+b<4 |
| minus | 0<=c<=floor((d-3)/2) | 4<a+b<5 |
| minus | floor((d-3)/2)+1<=c<=d-2 | 3<a+b<4 |

**Proof of the sum wall.** For m=3,4,5,6 define

    Q_m(t)=3t^2-(3r+2m+2)t+2eps.

The mixed identity gives Q_m(beta)=2beta(a+b-m). Direct polynomial
expansion (equivalently the determinant of multiplication by Q_m in the
cubic quotient) gives Res(chi,Q_m)=-8eps*P_m, with

| m | P_m on plus | P_m on minus |
|---|---|---|
| 3 | 3c^2-6c-12d^2+8d-9 | 3c^2+10c-12d^2-24d+7 |
| 4 | 6c^2+9cd-8c-6d^2-6d-14 | 6c^2+9cd+36c-6d^2+2d+54 |
| 5 | 9c^2+18cd-6d-25 | 9c^2+18cd+72c+42d+143 |
| 6 | 12c^2+27cd+18c+6d^2+8d-30 | 12c^2+27cd+118c+6d^2+96d+286 |

Here chi(t)=t^3-(r+3)t^2+(n-3d+3eps+2)t-2eps.
To justify the resultant's sign, rather than merely calculate its value,
put C=3r+2m+2 and s=r+3-beta<1. The quadratic factor of chi at beta has
trace s and product 2eps/beta. Algebraic norm expansion in that quadratic
quotient gives

    Norm_quadratic(Q_m) = (2eps/beta)*N,
    N=C^2-C*(beta+3)*s+3beta*s^2+eps*(2beta-12+18/beta).

This identity follows by eliminating the quadratic's degree-two terms using
its trace and product. It needs no numerical embeddings. Since beta>2,
beta<r+5, m>=3 and r>=3,

    N > C*(C-beta-3)-(2beta+21)
      > 2r*C-(2r+31) > 0.

Thus the quadratic norm has sign eps, and
sign(a+b-m)=-sign(P_m). Irreducibility also excludes Q_m(beta)=0:
Q_m is a nonzero polynomial of degree two.

P_3<0 throughout: on plus its maximum on 0<=c<=d+4 is at an endpoint,
with values -12d^2+8d-9 and -9d^2+26d+15, both negative for d>=7;
on minus its increasing maximum at d-2 is -9d^2-26d-1.
P_6>0 by its displayed coefficients and d>=7. On plus, P_5(0)=-6d-25<0,
P_5(1)=12d-16>0 and P_5 increases for c>=0. On minus P_5>0.
P_4 increases in integer c for both signs. Write d=2k or 2k+1;
its values at the last claimed negative index and the next index are

| sign | parity | last negative index | P_4 there | P_4 at next index |
|---|---|---|---|---|
| plus | d=2k | c=k | -20k-14 | 10k-16 |
| plus | d=2k+1 | c=k+1 | -5k-19 | 25k |
| minus | d=2k | c=k-2 | 6-20k | 10k+24 |
| minus | d=2k+1 | c=k-1 | 11-5k | 25k+50 |

These signs are strict for all allowed d>=7. This proves the partition.

#### Integer data for all six nonaligned seeds

All windows below include both integer endpoints. Define the following
**integers**, obtained from R_C and the sum wall just proved:

    B=floor(b): 2 at plus c=0; 1 elsewhere.
    T=floor(2b): 4 at plus c=0; 3 at plus 1<=c<=d;
                 2 at plus d+1<=c<=d+4; 3 on minus.
    M=floor(a+b): the five-row partition above.
    g=floor(Delta): 1 at plus c=0,1; 0 elsewhere.
    z=0 on plus, 1 on minus; q=1 on plus, 2 on minus.

All these quantities lie in strict open unit chambers: none is an equality
wall. The two nonaligned seeds for each A>B in length order are

    D_AB=(A,A,ell_B), N_AB=(B,A,ell_B-ell_A).

The complete, **distinct** first-child sets are the unions of the rows for
that seed in the following tables. F/R/L mean first singleton/y-run/last
singleton of the *expanded words*. Run indices i,j start at zero.

| seed | segment pair | child | exact integer window |
|---|---|---|---|
| D_xc=(x,x,b) | R/F | (y,x,n+b-i) | n+B<=i<=n+M |
| | R/R | (y,y,n+a+b-k), k=i-j | n+M<=k<=n+M+1 |
| | L/R | (x,y,a+b-d+j) | d-M-1<=j<=d-B-1 |
| N_xc=(c,x,-Delta) | F/R | (c,y,b-d+j) | d-B-1<=j<=d-1 |
| | R/R | (y,y,0), j-i=d | one distinct child |
| | L/L | (x,x,0) | one pair |

For the two positive y-offset seeds use H=2d-eps for D_xy, H=d-eps
for D_cy:

| seed | segment pair | child | exact integer window |
|---|---|---|---|
| D_xy=(x,x,1) | R/F | (y,x,r+h-i) | r+z<=i<=r+T |
| | R/R | (y,y,beta-k), k=i-j | r+T<=k<=r+T+1 |
| | L/R | (x,y,2b-H+j) | H-T-1<=j<=H-q |
| D_cy=(c,c,1) | R/F | (y,c,r+b-i) | r+B<=i<=r+T |
| | R/R | (y,y,beta-k), k=i-j | r+T<=k<=r+T+1 |
| | L/R | (x,y,2b-H+j) | H-T-1<=j<=H-q |

For N_xy and N_cy use the same respective values H=2d-eps, d-eps:

| seed | segment pair | child | exact integer window |
|---|---|---|---|
| N_xy=(y,x,1-a) and N_cy=(y,c,1-b) | F/R | (c,y,h-H+j) | H-q<=j<=H+g |
| | R/R | (y,y,k-H-Delta), k=j-i | H+g<=k<=H+g+1 |
| | R/L | (y,x,r-Delta-i) | r-g-1<=i<=r-1 |
| | L/L | (c,x,-Delta) | one pair |

The two N_y tables have identical physical child expressions and different
H-dependent occurrence witnesses. After renaming j-H or k-H their distinct
child sets actually agree. Their expanded words and occurrence counts need
not agree.

#### Completeness, clipping, strictness and duplicate identification

Here is an exhaustive segment-pair argument, independent of any graph.
For a parent with inflated displacement S, first lengths h_A,h_B, run
lengths R_A,R_B and last starts f_A=h_A+R_A, f_B=h_B+R_B,
there are exactly nine F/R/L segment-pair kinds.

For a singleton of length u at U against a bottom run starting h_B,
put C=S+h_B-U. The exact F/R or L/R condition is

    -C-1 < j < u-C,     0<=j<=R_B-1.

For a top run starting h_A against a singleton of length v at V,
put C=S+V-h_A. The R/F or R/L condition is

    C-1 < i < C+v,      0<=i<=R_A-1.

For R/R put C=S+h_B-h_A and k=j-i. The exact condition and attainability are

    -C-1 < k < 1-C,     1-R_A<=k<=R_B-1;
    i=max(0,-k), j=i+k is an actual occurrence witness.

Singleton/singleton pairs have their single displacement and the same strict
overlap guard. These formulas classify every occurrence pair, not just a
superset of potential labels.

For D_xc, S=a+b+n. Substitution in these guards gives
n+b-1<i<n+a+b; n+a+b-1<k<n+a+b+1 (here k=i-j);
and d-a-b-1<j<d-b, yielding precisely its table.
For N_xc, S=-d-Delta. F/R gives d-b-1<j<d, R/R gives k=d
(with k=j-i), and the common final x starts coincide. R/L and L/R
are *endpoint tangencies* at their run ends and fail the strict guard.

For D_xy and D_cy, S=beta=r+2b. Their R/F inequalities respectively are
r+h-1<i<r+2b and r+b-1<i<r+2b. R/R gives the two integers around
beta. L/R gives H-2b-1<j<H-h. Since h is strictly between 0 and 1
on plus, and between 1 and 2 on minus, these give the displayed bounds.
For N_xy, S=-(2d-eps)-2Delta; for N_cy, S=-(d-eps)-Delta.
Their F/R inequality is H-h-1<j<H+Delta, and R/R gives the two
integers around H+Delta. Their final bottom x begins Delta before
the top final c; R/L gives r-Delta-1<i<r+b, clipped to i<=r-1.
The common final endpoints give the listed L/L child.

**All absent segment pairs.** For every D seed, S is beyond the top first
tile, so F/F and F/R are disjoint. Its bottom last begins beyond the whole
top word, so F/L,R/L,L/L are disjoint. L/F is disjoint because respectively
(a+b)<d, 2b<2d-eps, or 2b<d-eps. The first follows from a+b<6<d;
the others from 2b<5 and d>=7. Exactly R/F,R/R,L/R remain.
For N_xc, the bottom first ends at b-d<0, excluding F/F,R/F,L/F;
F/L is beyond the first top tile; R/L and L/R are the tangencies already
excluded. For each N_y seed the bottom first ends at h-H<0, excluding
F/F,R/F,L/F; the bottom last begins beyond the top first end because
r>Delta, excluding F/L; the bottom run ends Delta before the top last
starts, excluding L/R. Exactly its four tabulated kinds remain.

**No omitted clipped indices.** B<=2,T<=4,M<=5,g<=1; r>=3;
n-r=d-eps>=6, p-r=2d-eps>=13, and d>=7. For D_xc,
all displayed i are in 0..p-1 and all j in 0..p-1; its largest
R/R difference n+M+1<=p-1 because M<=5<=d-2, witnessed by i=k,j=0.
For D_xy and D_cy the largest R/R k=r+T+1 lies respectively in
0..p-1 and 0..n-1, again witnessed by i=k,j=0. Their R/F windows
are smaller, and L/R windows lie inside their actual runs since their
lower endpoints are positive and H is strictly shorter than that run.
For N_xc the witness i=0,j=d is in the actual runs, as is every F/R index.
For N_y, the bottom run length is H+r; its largest R/R k=H+g+1 is
<=H+r-1 because r>=g+2. Use i=0,j=k. Its F/R window is smaller;
its clipped R/L window starts at r-g-1>=0. Thus every listed child
is realized and no formal infinite-run position has been admitted.

**Duplicates.** Within a table's non-R/R row, different indices give
nonzero integer multiples of ell_y in their displacements. In R/R,
all occurrence pairs with the same difference k give the *same* state;
different differences give distinct states. The listed segment kinds have
different ordered letter pairs, so cannot coincide across rows of one seed.
The tables count distinct states, not occurrence pairs. Different seeds may
share children, which is intentionally preserved.

Together with PR #404's three aligned tables, this is the exact first-generation
theorem for all nine seeds. The six new counts, in the order
D_xc,N_xc,D_xy,N_xy,D_cy,N_cy, are

    2M-2B+4, B+3,
    2T+4 (plus) or 2T+2 (minus), 8 if g=1 else 6 (plus) or 7 (minus),
    2T-B+4 (plus) or 2T-B+3 (minus), same count as N_xy.

#### Descendants: reusable transfer rules and a concrete failed carrier

The three strict-window rules above work for **any** interior-overlap parent.
Four singleton/singleton cases, four singleton/run cases of width <5, and
one difference window of width 2 enumerate all distinct children with at
most 26 candidates, after R/R multiplicities are collapsed. Actual run
bounds and strict endpoints are part of the rule. This is an exact reusable
transfer interface, not a proof that any proposed collection is closed.

The naive carrier consisting of the nine seeds and their first children
already fails at (d,eps,c)=(7,+1,0), n=9. It has 58 distinct states.
Its first-generation parent and a realized escaping child are

    parent = (x,y,a+b-6),
    child  = (x,c,3a-10b+10).

In the common scale (beta-2)(beta-1), their coefficient vectors in
1,beta,beta^2 are (-30,43,-6) and (-8,-72,10). The exact literal-word
oracle checks membership, the edge and the child's absence from that carrier.
This is an obstruction to **this finite candidate**, not to a richer
parameter-indexed carrier. The independent finite descendant experiment
inflates every distinct parent through generation 3, retaining generation 4,
at d=7, eps=+-1, c=0,1,2. It includes coincidence states and stops at a fixed
depth, regardless of whether a closure might exist later. No BH test is run.

### Evidence and replay

Canonical implementation: `kernel/psc/class_c_seed_interfaces.mojo`.
Its finite parameter interface refuses d outside 7..64 or c outside the lower
cone before arithmetic. It uses the existing exact cubic field, checked
coefficient arithmetic and unbounded-rational sign fallback, with no floats.
`sum_wall_resultant` evaluates the quotient norm using the existing Mat3
module; its fixed-width range is bounded in the source. Hand quantifiers
above remain all d>=7; the executable budget does not replace them.

From repository root:

    python3 oracles/python/check_class_c_seed_interfaces.py

From kernel/:

    pixi run --locked mojo run -I . tests/test_class_c_seed_interfaces.mojo
    pixi run --locked mojo run -I . class_c_seed_interfaces.mojo dump > /tmp/class-c-seeds.txt

Then from repository root:

    python3 oracles/python/check_class_c_seed_interfaces.py --mojo-dump /tmp/class-c-seeds.txt

The oracle imports only the earlier independent exact literal-prefix/Fraction
implementation, not the canonical windows. It compares every actual word
occurrence pair against a separate transcription of the tables, and, with
the dump, compares full canonical child sets. It also independently rebuilds
the depth-4 frontier and checks all exported descendant edges. Missing or
duplicate export records fail. The finite grid comprises 105 members and
945 interfaces: every c at d=7,8,9 and representatives on both sides of every
wall at d=16,31,64, including c=d,d+1,d+2,d+4 on plus.

The Mojo actual-occurrence regression separately covers 75 members / 675
interfaces at d=7,8,9,16. The descendant experiment covers 2,131 parents,
with a 4,096-state cap per member; an exhausted cap raises and supplies no
verdict. The packet `evidence/class-c-seed-interfaces-2026-10-30/` records the
bounded summaries and deterministic export digest. CI regenerates the export,
checks the packet and uploads the complete state/edge export. Successful
hosted jobs are required before integration; local results are not called
hosted acceptance.

### Negative controls

- The sum-wall crossings have opposite P_4 signs at adjacent integer
  parameters, including the close minus corner d=7,c=2 with P_4=-4.
- Plus c=1 -> 2 changes g and the two N_y child counts from 8 to 6.
- Plus c=d -> d+1 changes T and both positive y-offset child counts.
- Strict integer-window controls exclude both endpoints and test empty
  windows after actual-run clipping. A tangential parent is refused.
- Out-of-cone parameters, wrong signs and finite-budget violations refuse.
- Actual occurrence enumeration contains repeated children; treating its
  multiplicity as the distinct state count fails the differential check.
- The 58-state seeds-plus-first-layer candidate has the escaping edge above.
  No fixed-depth experiment is labelled a boundary-hitting certificate.

### Non-claims / remaining gaps

The one-generation formulas are quantified exactly on the stated cone.
The 105-member and depth-4 checks are bounded finite experiments. Neither the
26-child bound nor the reusable local transfer rules supply a forward-closed
parameter-uniform carrier, a decreasing hitting measure, or an all-depth state
bound. Further work must specify a typed parameter-indexed carrier and prove
its inclusion/closure, then give hitting paths or ranks and discharge the
separate realization and non-unit spectral bridges. No PSC completion status
or existing proof ledger claim is promoted by this contribution.
