# Q3: a singleton outgoing star and a five-edge typed exit

## Exact conclusion and dependency scope

Throughout the inherited class-A minus boundary chamber, Q3=(x,y,1,-1,1)
has **exactly one** strict occurrence-indexed child:
**(A+1,0)->X=(x,x,1,0,-1)**. Its actual reversal has exactly the reversed
edge (0,A+1)->R(X). There is no parameter-dependent split or unresolved
direct Q3 child. X has an established four-edge typed-coincidence exit;
therefore Q3 has an explicit exit of length five. This is an existence
bound, not a shortest-path assertion. The genuine cycle Q3->X->Q3 prevents
any all-edge strict-descent conclusion.

This packet extends PR #372 at
8e97ad5035072951259b0301e7387f8baf25d148, which depends on PR #365 at
e4f7fc767a45c9445c5294c16d7a703f75f43828. Preserve both historical evidence
packets. PR #365 passed all 68 recorded exact-head checks and was merged at
148e5b35730ffa979b7f017bfa09f5882b5b1b5b; #372 was retargeted to main
without changing its head or evidence. #372 remains open with incomplete
hosted gates; this Q3 increment stays stacked on it. Integration must proceed
in dependency order. Independent human
review remains pending and is distinct from project acceptance for progression.
The [stop/go](class-a-boundary-q3-stopgo-2026-10-28.md) reuses the scoped
three-primary-source actual-overlap review, with no new spectral transfer.

## Hypotheses, actual ancestry and prefixes

Integers k,t>=0, n=k+t+3, d=2n-1-k, A=n+d, N=n-1.
The ordered words are x->x y^A x, c->c y^n x, y->x y^N c.
Indices are zero-based. Offsets are full bottom-minus-top Parikh triples in
the (x,c,y) basis; reversal swaps types and indices and negates all coordinates.
Only strict physical intersection counts, with guard
-L(bottom child)<s<L(top child).

Use the established exact Perron embedding, Ly=1, h=1/beta,
alpha=beta-(n+2), rho=alpha-h, a=Lx=2+rho, b=Lc=1+h,
zeta=alpha-2h. Inherited results give 0<h<1/5, 0<rho<1,
0<zeta<rho and hence 2<a<3. No decimal approximation is used.
Q3 has shift a-b+1=a-h=2+zeta, with upper margin h>0
and lower margin a-h+1>0; its reversal is interior as well.

P3=(x,y,1,3,-4) has M offset (1,-1,d+4). Its LAST/RUN
(A+1,n-2) uses prefixes (1,0,A) and (1,0,n-3), so the child
is (x,y,1,-1,1). Here 1<=n-2<=N since n>=3, including the sole
n=3 member k=t=0. P3's complete star already proves strict overlap;
the current packet independently replays that actual edge and its reversal.

The incidence update is M(u,v,w)=(2u+v+w,v+w,A*u+n*v+N*w).
Thus M(Q3)=(2,0,A-1), and the inflated physical shift is
G=2a+A-1. Equivalently beta*(a-h)=beta*a-1=2a+A-1.
The symbolic implementation clears beta>0, using
beta*a=beta^2-n*beta-1 and beta*b=beta+1, and checks this identity
modulo the characteristic cubic over Q[t,k].

There is also a direct completeness check on the whole intervals. The source
overlap has length h, so its inflation has length beta*h=1. The inflated top
ends at beta*a=2a+A, and the bottom starts at G=beta*a-1. The top LAST x
starts at a+A, so G lies strictly inside it by a-1>0; the bottom FIRST x
ends at G+a>beta*a. Every earlier top child ends before G, and every later
bottom child starts after beta*a. Thus the length-one inflated intersection
lies in exactly this single actual child pair, independently confirming the
exhaustive nine-kind table below.

FIRST prefix is (0,0,0), RUN i prefix (1,0,i-1), LAST R+1 prefix
(1,0,R), for both parents x and y here. Their starts are 0,a+i-1,a+R.
Top R=A, bottom R=N. Top LAST is x; bottom LAST is c.

## Complete nine-kind symbolic classification

Every possible actual pair appears below; all RUN indices are bounded by
1<=i<=A and 1<=j<=N. The displayed target includes even disjoint candidates,
so the excluded cases retain their exact type and full transport.

| Kind | Actual indices | Typed child (top,bottom,u,v,w) | Physical shift s | Strict result |
| --- | --- | --- | --- | --- |
| FIRST/FIRST | (0,0) | (x,x,2,0,A-1) | A+2a-1 | none |
| FIRST/RUN | (0,j) | (x,y,3,0,A+j-2) | A+3a+j-2 | none |
| FIRST/LAST | (0,N+1) | (x,c,3,0,A+N-1) | A+3a+N-1 | none |
| RUN/FIRST | (i,0) | (y,x,1,0,A-i) | A+a-i | none |
| RUN/RUN | (i,j) | (y,y,2,0,A-1+j-i) | A+2a-1+j-i | none |
| RUN/LAST | (i,N+1) | (y,c,2,0,A+N-i) | A+2a+N-i | none |
| LAST/FIRST | (A+1,0) | X=(x,x,1,0,-1) | a-1 | **always** |
| LAST/RUN | (A+1,j) | (x,y,2,0,j-2) | 2a+j-2 | none |
| LAST/LAST | (A+1,N+1) | (x,c,2,0,N-1) | 2a+N-1 | none |

These are exact symbolic conditions, with no hidden root-order or parameter
test. Here is the exhaustive guard reduction. For excluded cases it suffices
to prove s-L(top child)>0. FIRST/FIRST gives A+a-1>0;
FIRST/RUN gives at least G>0; FIRST/LAST gives G+N>0.
RUN/FIRST gives at least a-1>0; RUN/RUN at least 2a-1>0;
RUN/LAST at least 2a+N-1>0. LAST/RUN gives at least a-1>0;
LAST/LAST gives a+N-1>0. For LAST/FIRST the two strict margins are
s+a=2a-1>0 and a-s=1>0. All follow from a=2+rho, rho>0,
N>=2 and A>=8. The Mojo certificate checks the Q[t,k] constant lower
bounds after this substitution; all omitted rho coefficients are nonnegative.
In particular the upper margin of the accepted child is exactly 1, not zero.

Reversal maps each pair (i,j) to (j,i), each kind to its transpose,
and s to -s, turning the strict interval into the reversed strict interval.
It is a bijection on literal word positions. Thus the reversed table has
only FIRST/LAST (0,A+1)->R(X), with the bottom LAST still the actual x.
No last ordinal is a RUN. All source and terminal types are checked.

The chamber-wide Q3 outgoing image is exactly {X,R(X)}, two distinct labels;
each orientation has a singleton star in every parameter member. The complete
transport and guards prove universal containment; k=t=0 already attains both.
Production synthesis emits one edge in O(1) operations, with checked member
arithmetic. The literal rectangular sweep is only a finite verification oracle.

## Every direct child's bounded typed tail and a genuine cycle

X is the existing X of
[the W/Z/X/Q classification](class-a-boundary-w-carrier-2026-10-27.md),
not a newly unclassified family. Keep the old name Q=(y,x,0,-1,1)
distinct from Q3. Reuse the classified X star and established V/W/Q suffix:

| Source | Actual kind and indices | Full target | Target physical shift |
| --- | --- | --- | --- |
| Q3 | LAST/FIRST (A+1,0) | X=(x,x,1,0,-1) | a-1 |
| X | RUN/FIRST (d,0) | V=(y,x,0,-1,2) | 1-h |
| V | LAST/FIRST (n,0) | W=(c,x,0,1,-1) | h |
| W | RUN/FIRST (1,0) | Q=(y,x,0,-1,1) | -h |
| Q | RUN/RUN (1,2) | C=(y,y,0,0,0) | 0 |

The corresponding incidence images before prefix correction are
(2,0,A-1), (1,-1,d+1), (1,1,n-2), (0,0,1), (0,0,-1).
Subtracting the displayed actual top prefixes and adding bottom prefixes gives
each full target. Word legality holds on the entire cone: 1<=d<=A,
V's top y LAST index is n=N+1, c has run 1, and the last pair has
1<=N and 2<=A. Every intermediate is strictly interior: X has margins
2a-1 and 1; V has margins a+1-h and h; W has margins a+h and b-h=1;
Q has margins a-h and 1+h; C has both margins 1. These margins are positive
from the inherited bounds. Symbolic transport verifies every step and its
actual reversal over Q[t,k]; literal tests verify the actual words and geometry.

Consequently **every direct Q3 child has a typed-coincidence tail of length
four**; none remains unresolved at this direct-child scope. This is stronger
than success for selected first choices because there is only one first choice.
It says nothing about productivity of every later successor or all P3 children.

X also has its genuine LAST/RUN (A+1,n+1)->Q3. The bottom RUN is legal:
A-(n+1)=d-1>=4. Its prefix correction is (0,0,n-A), so
(1,-1,d+1)+(0,0,n-A)=(1,-1,1), with actual types x/y. Q3's shift
and upper margin h prove strictness. Together with the singleton Q3 edge this
is a two-cycle in every member and in both orientations. A strict rank on every
edge is impossible. The outgoing two-label image is **not forward closed**:
X(d,0)->V lies outside {X,R(X)}. This does not settle the different 37-label
image of PR #372, whose forward closure remains unproved.

## Evidence, controls and deterministic replay

Canonical module: kernel/psc/class_a_boundary_q3_children.mojo, with matching
driver, native regression and .github/workflows/class-a-boundary-q3.yml.
Locked Mojo 1.1.0.dev2026090805: 56 members k=0..7,t=0..6,
112 oriented source cells, **33,096 candidate pairs / 112 accepted**,
560 selected path edges and 224 cycle-edge replays. Every actual word pair,
accepted target, ancestry edge and reversed accepted edge is checked with full
Parikh transport and exact Perron geometry. The symbolic certificate is the
all-parameter algebra check; these counts are finite implementation validation.

Independent literal-word/integer-polynomial/Fraction oracle: 117 members
k=0..12,t=0..8, 234 oriented cells, **122,616 pairs / 234 accepted**,
1,170 selected path edges and 468 cycle-edge replays. It separately validates
the four-edge tail from every actual direct child. Its fixed 512-refinement
sign budget refuses inconclusively on exhaustion. Both orientations' image
labels have recorded actual witnesses. No floating-point decisions or Mojo
guard output enters the independent geometry.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_q3_children.mojo
pixi run --locked mojo run -I . class_a_boundary_q3_children.mojo
cd ..
python -m pytest -q tests/test_class_a_boundary_q3_children.py
python oracles/python/class_a_boundary_q3_children.py > /tmp/q3-children.json
cmp /tmp/q3-children.json evidence/class-a-boundary-q3-2026-10-28/probe.json
sha256sum -c evidence/class-a-boundary-q3-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-q3-2026-10-28/SHA256SUMS
bash tools/verify_all.sh provenance
```

Controls reject legal but disjoint Q3 LAST/RUN (A+1,1), wrong interior
x/c target (1,0,-1) at its real x/x child, invalid orientations or ordinals,
negative parameters, duplicate singleton packets, a LAST falsely supplied as
RUN, corrupted field identity, altered intermediate, truncated path and
unequal-type zero terminal. Old Q's FIRST/RUN (0,2) has exact shift a,
so endpoint contact is excluded; old Q(n,n+1) is a real c/y zero-offset
overlap and is refused as typed coincidence. X has matching x/x types but
nonzero offset and is also not coincidence. The actual two-cycle is retained
as a counter-calibration to all-edge descent.

Full receipts, replay output, source digests and dependency/check snapshots
are archived in evidence/class-a-boundary-q3-2026-10-28/. Local formal and
provenance outcomes are recorded in its README; a failed Lean launcher earns
no proof pass. No Lean/TLA source, governed status or named proof is changed:
preserve 124 governed claims, 34 named proofs and 325 source openings.
Fresh exact-head hosted gates are required before dependent integration.

## Remaining scope boundary

The direct Q3-child productivity question is discharged. All remaining P3
children and the 37-label image retain their previous unresolved obligations;
this singleton result cannot certify them. All-source cyclic strict-zipper,
plus chambers, target-aware BH, non-unit internal-space/return-lattice
realization, universal BH/#139, A1-prime, G1 and PSC remain open.
Independent human review pending.
