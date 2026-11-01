# R3 and D3: complete stars, typed exits and carrier reconciliation

## Scope, hypotheses and dependencies

Continue #373 at 2fc615cb923a6152cf390ef92ef9788a346af544, with #372's
P3 classification preserved at 8e97ad5035072951259b0301e7387f8baf25d148.
Their exact-head hosted acceptance remains required before dependent integration.
Independent human review pending. No governed claim or formal-source promotion.
The [stop/go](class-a-boundary-r3-stopgo-2026-10-28.md) reuses the existing
three-primary-source actual-overlap and non-unit hypothesis review.

Keep integers k,t>=0, n=k+t+3, d=2n-1-k, A=n+d, N=n-1, and ordered
words x->x y^A x, c->c y^n x, y->x y^N c. Offsets are full
bottom-minus-top Parikh triples in the (x,c,y) basis. Every edge retains
actual zero-based occurrence indices and the strict guard
-L(bottom child)<s<L(top child). Reversal transposes types and indices and
negates all three coordinates, not just the physical shift.

Inherited exact quantities are h=1/beta, alpha=beta-(n+2), rho=alpha-h,
a=Lx=2+rho, b=Lc=1+h, Ly=1, zeta=alpha-2h, u=a-b=1+zeta.
The certified bounds are 0<h<1/5, 0<zeta<rho<1, 0<alpha<1 and
0<alpha+h<1. These are ordered algebraic inequalities, with no decimal
root approximation and no independence assumption on the tile lengths.

The new sources are R3=(x,y,1,-1,0), with shift u=1+zeta, and
D3=(x,c,1,-1,-1), with shift zeta. Both are strictly interior on the entire
cone. R3's upper margin is a-u=b>0; D3 has positive shift below a.

## Reconcile the 39-label candidate before expanding it

The candidate S39 is the complete 37-label P3 outgoing image plus
X=(x,x,1,0,-1) and R(X). The source registry binds explicit complete-star
interfaces in the P3, Q3, W/X, U/V, E/H, T_m, P and H3 modules. An
unregistered label means no complete-star interface is bound in this registry;
it does not assert that every other mechanism in the repository is inapplicable.
Registered exits and complete stars are separate facts. Terminal C is counted
separately rather than requiring expansion of its coincidence descendants.

| Registered family in S39 | Oriented labels | Existing evidence |
| --- | --- | --- |
| C=(y,y,0,0,0) | 1 | typed terminal |
| T=(y,x,0,-1,1), U=(x,x,0,-1,1), V=(y,x,0,-1,2), and reversals | 6 | P3 and U/V complete stars; selected exits |
| E=(x,x,0,0,1) and reversal | 2 | E/H complete stars and exits |
| T1=(y,y,-1,1,1), T2=(y,y,-1,1,2), and reversals | 4 | T_m complete stars; T1 has the W packet's selected suffix; no uniform T2 exit is registered here |
| Q3 and reversal | 2 | singleton stars and five-edge exits |
| X and reversal | 2 | W/X complete stars and four-edge exits |

Before this increment: **16 registered nonterminal stars plus one terminal**,
and **22 unregistered labels**. Fourteen nonterminal labels have registered
uniform exits; T2 and its reversal have registered stars without such an exit.

The 22 missing star interfaces fall into these exact families; each row
includes the actual reversals, with r varying over the displayed values:

| Base label | r | Oriented labels before this packet |
| --- | --- | --- |
| (y,x,0,-1,r) | -1,0 | 4 |
| (x,x,0,-1,r) | -1,0 | 4 |
| (x,y,1,-1,r) | -2,-1,0 | 6 |
| (x,y,1,0,-1) | fixed | 2 |
| (c,y,0,0,r) | 0,1 | 4 |
| (y,x,0,0,0) | fixed | 2 |

R3 is the r=0 member of the third row. Classifying its two orientations
raises S39 to 18 registered nonterminal stars plus C, leaving 20 unregistered.
Adding the new D3 and R(D3) gives S41 with 20 registered nonterminal stars,
C, and 20 unregistered labels. The complete 39-row before/after reconciliation
is machine-readable in the independent probe's `reconciliation` object.
These are registry coverage counts, not a finite-carrier or global BH theorem.

## Actual ancestry and exact field transport

Use M(p,q,r)=(2p+q+r,q+r,A*p+n*q+N*r). Full incidence images and
inflated physical shifts are:

| Source | M offset | Inflated shift G |
| --- | --- | --- |
| R3 | (1,-1,d) | d+u=d+1+zeta |
| D3 | (0,-2,n-k) | t+1-2h |

The kernel clears beta>0 using beta*a=beta^2-n*beta-1 and beta*b=beta+1.
It verifies beta*G(R3)=beta^2+(d-n-1)*beta-2 and
beta*G(D3)=(t+1)*beta-2 modulo the characteristic cubic over Q[t,k].

R3 has uniform, literal X ancestry: X(A+1,n)->R3. X's incidence offset
(1,-1,d+1) gains (0,0,n-1-A), leaving (1,-1,0). The bottom n is a real
RUN of sigma(x), since A-n=d>=5. This includes n=3 and both reversals.

P3(A+1,n-3)->R3 is also actual when n>=4. Here bottom prefix
(1,0,n-4) minus top (1,0,A) changes (1,-1,d+4) to (1,-1,0).
The source certificate checks the union of shifted k and t cones covering
n>=4. At n=3, n-3=0 is FIRST x, and the actual child is
U=(x,x,0,-1,1), not R3. The wrong RUN/type claim is explicitly refused.

R3(A+1,n)->D3 is LAST/LAST: top LAST x and bottom LAST c, with prefixes
(1,0,A) and (1,0,N). Subtracting them from (1,-1,d) leaves (1,-1,-1).
Its shift is zeta>0, so this actual child is strict everywhere.

## Complete nine-kind classification of R3

Top FIRST/RUN/LAST starts are 0,a+i-1,a+A; bottom starts are
0,a+j-1,a+N. RUN bounds are 1<=i<=A and 1<=j<=N.
Every syntactic candidate is included below, even when disjoint.

| Kind | Full typed child | Shift s | Accepted indices |
| --- | --- | --- | --- |
| FIRST/FIRST | (x,x,1,-1,d) | G | none |
| FIRST/RUN | (x,y,2,-1,d+j-1) | G+a+j-1 | none |
| FIRST/LAST | (x,c,2,-1,d+N) | G+a+N | none |
| RUN/FIRST | (y,x,0,-1,d-i+1) | d-h-i | i=d-1..d+2, j=0 |
| RUN/RUN | (y,y,1,-1,d+j-i) | d+1+zeta+j-i | i-j=d+1,d+2 |
| RUN/LAST | (y,c,1,-1,d+N-i+1) | G+N-i+1 | none |
| LAST/FIRST | (x,x,0,-1,-n) | -n-b | none |
| LAST/RUN | (x,y,1,-1,j-n-1) | zeta+j-n | (A+1,N) |
| LAST/LAST | D3=(x,c,1,-1,-1) | zeta | (A+1,n) |

RUN/FIRST's exact strict bounds are d-1-h<i<d+2+zeta, giving
d-1..d+2, all legal since d>=5 and n>=3. RUN/RUN requires
d+zeta<i-j<d+2+zeta, giving exactly d+1,d+2. For each delta use
1<=j<=min(N,A-delta): these are n-1 and n-2 occurrences.
LAST/RUN requires j>n-1-zeta; the true bottom bound j<=N forces j=N.
Its shift is zeta-1 in (-1,0). LAST/LAST has shift zeta in (0,1),
strictly inside (-b,a).

The exclusions are exact. G>=d+1>a rules out every FIRST case; adding a
bottom prefix increases it. RUN/LAST is at least 1+zeta>1. LAST/FIRST's
lower margin is a-n-b=u-n<0, since u<2<n. Thus the count per orientation
is 4+(n-1)+(n-2)+1+1=**2n+3**, with eight distinct labels per member.
Actual reversal transposes all nine kinds and indices and preserves strictness.

## Complete nine-kind classification of D3

Let L=n-k=t+3. The bottom word is sigma(c)=c y^n x: its FIRST type
is c, not x, and its RUN/LAST prefixes are (0,1,j-1), (0,1,n), with
starts b+j-1,b+n. Top RUN count is A and bottom RUN count is n.

| Kind | Full typed child | Shift s | Accepted indices |
| --- | --- | --- | --- |
| FIRST/FIRST | (x,c,0,-2,L) | t+1-2h | (0,0) iff t<=1 |
| FIRST/RUN | (x,y,0,-1,L+j-1) | t+j+1-h | (0,1) iff t=0 |
| FIRST/LAST | (x,x,0,-1,L+n) | t+n+2-h | none |
| RUN/FIRST | (y,c,-1,-2,L-i+1) | t-i-alpha-h | i=max(1,t-1)..t, j=0 |
| RUN/RUN | (y,y,-1,-1,L+j-i) | t-alpha+j-i | i-j=t-1,t |
| RUN/LAST | (y,x,-1,-1,L+n-i+1) | t+n+1-alpha-i | i=n+t..n+t+2, j=n+1 |
| LAST/FIRST | (x,c,-1,-2,L-A) | G-a-A | none |
| LAST/RUN | (x,y,-1,-1,L+j-1-A) | t-alpha+j-1-A | none |
| LAST/LAST | (x,x,-1,-1,L+n-A) | t-alpha-d | none |

FIRST/FIRST's lower margin is t+2-h>0; its upper bound is
t<1+alpha+h, hence t<=1. FIRST/RUN's strict upper bound is
t+j<1+alpha, hence exactly t=0,j=1. FIRST/LAST exceeds a by
t+n-alpha>0.

For RUN/FIRST put v=alpha+h in (0,1). The bounds are
t-v-1<i<t+1-alpha, giving i=t-1,t before clipping to 1..A.
Thus there are zero, one, two such occurrences at t=0, t=1, t>=2.
RUN/RUN gives i-j=t-1,t. For each delta, use
max(1,1-delta)<=j<=n and i=j+delta. The upper top bound is automatic
from d>=t+5. At t=0 these strips have n-1 and n members; for t>=1
both have n. RUN/LAST's bounds are n+t-alpha<i<n+t+3-h,
giving exactly the three listed true RUN indices; A-(n+t+2)=n>0.

LAST/FIRST's lower margin is t-alpha-A<0. LAST/RUN's lower margin
is at most t-alpha-d<0. LAST/LAST's lower margin is
t-d+2-h=-k-t-3-h<0. Hence none of the LAST cases intersects.
The count is **2n+4 at t=0**, and **2n+5 at t>=1**. In each member
there are seven distinct labels per orientation, drawn from ten chamber-wide
base labels. The t=0/1 endpoints are not omitted or treated as RUNs.

## Full image, bounded exits and unresolved targets

The exact chamber-wide outgoing union of both families and their reversals
has **36 labels**, from these 18 base labels and their distinct reversals:

| Source | Complete base targets |
| --- | --- |
| R3 | (y,x,0,-1,r), r=-1..2; (y,y,1,-1,r), r=-2,-1; (x,y,1,-1,-2); D3 |
| D3 | (x,c,0,-2,r), r=3,4; H3=(x,y,0,-1,3); (y,c,-1,-2,r), r=4,5; P0=(y,y,-1,-1,3); P1=(y,y,-1,-1,4); (y,x,-1,-1,r), r=2,3,4 |

Containment follows by substitution into the complete strict index ranges;
the probe records an actual k,t,kind,i,j witness attaining every label.
This is a union over the chamber, not 36 labels in each parameter member.
Synthesis uses O(n) strips/endpoints and a fixed scalar target predicate.

Uniform selected paths, with actual reversals at every step, are:

* R3(d,0)->T=(y,x,0,-1,1), then T(1,2)->C. Length two.
  The new first target has shift -h, strictly inside (-a,1).
* D3(t+1,1)->P0=(y,y,-1,-1,3), whose shift is -alpha in (-1,0).
  This is a legal RUN/RUN edge since t+1<=A and 1<=n. Reuse the
  existing exact P0 exit: five further edges at k=0, three at k>=1.
  Thus D3 has length six at k=0 and four at k>=1 along this selected path.

For clarity, P0 is `p_source(0)` (called P in the earlier derivation),
and P1 is `p_source(2)` (earlier Pplus). At k=0 the P0 suffix is
P0(0,t+2)->D(t+2,0)->K(k+1,0)->L(0,n-2)->H1(1,2)->C.
At k>=1 it is P0(1,t+3)->B2h(0,N)->H1(1,2)->C. Its prior certificate
preserves the k=0 LAST/RUN distinction; this packet does not replace it by
an illegal uniform shortcut. New symbolic first transitions and all literal
path steps are checked; prior selected suffix certificates are reused.

The outgoing targets with registered uniform exits are R3's V, T, R(T1)
and D3, and D3's H3, P0 and P1, together with their reversals: **14 of the
36 labels**. R(T2) and T2 have complete stars but no uniform exit is
registered here. The following remaining target families, with reversals,
have no uniform exit certificate supplied by this packet:

| From source | Remaining base targets |
| --- | --- |
| R3 | (y,x,0,-1,r), r=-1,0; R(T2)=(y,y,1,-1,-2); (x,y,1,-1,-2) |
| D3 | (x,c,0,-2,r), r=3,4; (y,c,-1,-2,r), r=4,5; (y,x,-1,-1,r), r=2,3,4 |

There are **22 outgoing labels without a registered uniform exit** here.
This is an explicit proof-coverage gap, not evidence of unproductivity.
Neither selected source exit proves every direct child productive.
Both new sources have no immediate typed coincidence: every child has
c-coordinate -1 or -2 (and the reverse has +1 or +2).

## Successive actual escapes: neither enlargement closes the carrier

R3 belongs to S39, but its actual LAST/LAST child D3 does not. This
uniformly refutes forward closure of S39. If D3 and its reversal are added,
the resulting S41 still escapes: D3(t+1,1)->P0 lies outside S41.
Both P0 and its reversal are already independently classified source families,
so this second escape calls for reuse of existing work, not reclassification.
The native inventory verifies exact list nonmembership; the independent oracle
uses the separately written predecessor envelope and explicit tuples.

The earlier genuine Q3/X cycle remains intact. No all-edge rank or closed
obstruction is inferred. A candidate can contain productive states and still
fail forward closure; these examples retain that distinction concretely.

## Evidence, controls and replay

Canonical module kernel/psc/class_a_boundary_r3_children.mojo, matching
driver/regression and .github/workflows/class-a-boundary-r3.yml.
Locked local Mojo 1.1.0.dev2026090805: 56 members k=0..7,t=0..6,
224 oriented source cells, **69,104 candidate pairs / 5,136 accepted**,
700 selected path edges, all 36 image labels attained. Every literal pair is
compared with full Parikh transport and strict exact Perron-field geometry.
The symbolic certificate checks Q[t,k] transport, field identities, actual
index bounds, shifted t/k cones, typed selected first edges and ancestry.
The universal strict-guard proof is the reduction above, not a finite census.

Independent literal-word/integer-polynomial/Fraction oracle: 117 members
k=0..12,t=0..8, 468 source cells, **253,188 pairs / 14,014 accepted**,
1,440 selected path edges. It independently verifies all accepted/rejected
word pairs, every reversed accepted edge, source ancestry, carrier escapes,
36-label attainment and the exact source-registry counts. Its fixed
512-refinement sign budget refuses inconclusively on exhaustion.

Negative controls reject the disjoint legal R3 RF(d-2,0), changed interior
P1 target at D3's real P0 edge despite matching types and image membership,
n=3 P3 ordinal zero falsely supplied as RUN, t=0 RF ordinal zero, invalid
orientations/parameters/indices, duplicate or incomplete indexed stars,
corrupted field identity, changed intermediates, truncated paths and unequal-type
zero terminals. Tests retain t=0's FR edge, t=1's FF edge, and the failure of
both corresponding overstrong uniform rules.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_r3_children.mojo
pixi run --locked mojo run -I . class_a_boundary_r3_children.mojo
cd ..
python -m pytest -q tests/test_class_a_boundary_r3_children.py
python oracles/python/class_a_boundary_r3_children.py > /tmp/r3.json
cmp /tmp/r3.json evidence/class-a-boundary-r3-2026-10-28/probe.json
sha256sum -c evidence/class-a-boundary-r3-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-r3-2026-10-28/SHA256SUMS
bash tools/verify_all.sh provenance
```

Local native, scoped Python, formal attempts, full provenance, source digests
and dependency snapshots are archived in evidence/class-a-boundary-r3-2026-10-28/.
The README distinguishes completed passes from unavailable/incomplete checks.
No full-suite pass is inferred from the scoped results; local Lean fails before
compilation and earns no proof pass. Fresh exact-head hosted gates remain
required before integration, in dependency order.

## Remaining scope and next actual packet

The next uniform uncovered source can be chosen without guessing a word event:
B3=(y,x,0,-1,0) is R3's actual RUN/FIRST child (d+1,0) throughout the
cone. It has shift -b, with positive lower margin a-b=u>1. Its complete
star and uniform typed exit are not supplied here. All other unregistered
stars/exits remain explicit in the inventory and outgoing-target tables.

All-source cyclic strict-zipper coverage, plus chambers, target-aware BH,
non-unit internal-space/return-lattice realization, universal BH/#139,
A1-prime, G1 and PSC remain open. Preserve 124 governed claims, 34 named
Lean proofs and 325 source openings; independent human review pending.
