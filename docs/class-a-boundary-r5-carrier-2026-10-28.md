# R5: complete oriented stars and inherited three-edge exits

## Scope and dependencies

Continue #379 at 7eb395cce20973c2c36bef09c97b3d6ae8e57067. Its exact-head
hosted gates remain queued; they are required before dependent integration.
Independent human review remains pending validation debt. The
[stop/go](class-a-boundary-r5-stopgo-2026-10-28.md) reuses the existing
three-primary-source actual/every-overlap and non-unit review. No governed
claim, formal proof or source-opening count is promoted.

For integers k,t>=0 let n=k+t+3, d=2n-1-k=k+2t+5, A=n+d and N=n-1.
Keep the ordered words x->x y^A x, c->c y^n x, y->x y^N c.
A label records top/bottom types and the full bottom-minus-top Parikh vector
in (x,c,y). Every occurrence is actual and zero-based: FIRST 0, RUN 1..count,
LAST count+1. Strict intersection is -L(bottom)<s<L(top).
Reversal swaps types and indices and negates all three coordinates.

Use inherited exact h=1/beta, alpha=beta-(n+2), rho=alpha-h,
zeta=alpha-2h, z=alpha+h, a=Lx=2+rho, b=Lc=1+h, Ly=1.
The needed strict bounds are 0<h<1/5, 0<zeta<rho<1 and 0<z<1.
They are exact ordered algebraic bounds, without decimal root decisions,
analytic transfer or tile-length independence.

R5=(x,y,1,-1,-1) has shift a-b-1=zeta in (0,1), hence is strict
throughout the cone. Its existing complete ancestry is
Y4 LAST/RUN (A+1,N)->R5, valid even at n=3. Its existing selected exit
has three edges. This increment classifies the complete star, not a new exit.

## Full incidence and physical transport

The incidence action is M(p,q,r)=(2p+q+r,q+r,A*p+n*q+N*r).
Thus M(R5)=(0,-2,t+3) and its inflated shift is G=t+1-2h.
Clearing beta uses beta*a=beta^2-n*beta-1 and beta*b=beta+1;
the exact identity beta*G=(t+1)*beta-2 is checked modulo the cubic over Q[t,k].
Both oriented source field identities and all nine prefix transport formulas
are certified. Prefix expressions are affine in each RUN index; checking their
constant and index coefficients is implemented by the two independent symbolic
ordinal evaluations 1 and 2, in both coordinates. The complete symbolic word
prefix kernel supplies actual index bounds. Selected representative transitions
add uniform RR/RL, FF faces t=0/1 and RF shifted t>=0/1/2 cones; finite grids
are independent implementation validation, not extrapolation of the theorem.

Top FIRST/RUN/LAST starts are 0, a+i-1, a+A; bottom starts are
0, a+j-1, a+N. Both FIRST types are x; top LAST is x, bottom LAST is c.
R5 has D3's full source offset but a different actual bottom prefix and endpoint.
No D3 child classification is substituted for this table.

## Complete nine-kind table

RUN bounds are 1<=i<=A and 1<=j<=N.

| Kind | Full typed child | Shift s | Accepted indices |
| --- | --- | --- | --- |
| FIRST/FIRST | (x,x,0,-2,t+3) | G | (0,0) iff t<=1 |
| FIRST/RUN | (x,y,1,-2,t+j+2) | G+a+j-1 | none |
| FIRST/LAST | (x,c,1,-2,t+N+3) | G+a+N | none |
| RUN/FIRST | (y,x,-1,-2,t+4-i) | t-i-z | i=max(1,t-1)..t+1, j=0 |
| RUN/RUN | (y,y,0,-2,t+3+j-i) | G+j-i | i-j=t,t+1 |
| RUN/LAST | (y,c,0,-2,t+N+4-i) | t+n+1-2h-i | i=n+t,n+t+1, j=n |
| LAST/FIRST | (x,x,-1,-2,t+3-A) | G-a-A | none |
| LAST/RUN | (x,y,0,-2,t+j+2-A) | t+j-A-2h | none |
| LAST/LAST | (x,c,0,-2,t+N+3-A) | G+N-A | none |

FIRST/FIRST's lower bound is automatic and its upper bound is t<1+z;
since 0<z<1, exactly t=0,1 survive. FIRST/RUN requires t+j<2h,
impossible for j>=1. FIRST/LAST exceeds a because G+N>0.

RUN/FIRST bounds are t-1-z<i<t+2-2h. Since 0<z<1 and
0<2h<1, the exact integer interval is t-1..t+1, clipped to actual RUNs.
It has one occurrence at t=0, two at t=1 and three at t>=2.
Its upper bound is always within A. At t=1, nominal i=t-1=0 is actual
FIRST x, not RUN y. The true edge is strict FIRST/FIRST (x,x,0,-2,4),
not K=(y,x,-1,-2,5). At t=0 nominal i=-1 is unavailable, while i=0
is the true FIRST/FIRST edge with another offset. Preserve these real endpoints.

RUN/RUN's strict bounds t-2h<i-j<t+2-2h give exactly t,t+1.
Each strip contains every j=1..N. The largest top index is
N+t+1=n+t, and A-(n+t)=d-t=k+t+5>0.
RUN/LAST's bounds n+t-2h<i<n+t+2-h give exactly n+t,n+t+1.
Both are actual RUNs: A-(n+t+1)=k+t+4>0. Their target shifts are
1-2h and -2h, strictly inside (-b,1).

LAST/FIRST's lower margin is G-A<0. LAST/RUN has shift at most
t+N-A-2h=t-d-1-2h<-1. LAST/LAST's lower margin is
t-d+1-h=-k-t-4-h<0. Thus all LAST-top candidates are disjoint.
No strict guard has an omitted equality case.

The occurrence count is therefore
1+1+2N+2=2n+2 at t=0,
1+2+2N+2=2n+3 at t=1, and
0+3+2N+2=2n+3 at t>=2.
Reversal transposes this entire table and preserves both counts and strictness.
Canonical synthesis streams the true O(n) strips and endpoints, with no
quadratic search in the production star generator.

## Exact chamber-wide image and reused proofs

The union has 18 distinct labels: the following nine bases and their actual
reversals. It is a chamber union, not eighteen distinct labels in each member.

| Kind | Base labels | First attainment |
| --- | --- | --- |
| FF | (x,x,0,-2,r), r=3,4 | t=0,1 respectively; i=j=0 |
| RF | (y,x,-1,-2,r), r=3,4,5 | t>=0,1,2 respectively; i=t+4-r,j=0 |
| RR | (y,y,0,-2,r), r=3,2 | (t+1,1), (t+2,1) throughout |
| RL | (y,c,0,-2,r), r=3,2 | (n+t,n), (n+t+1,n) throughout |

Containment follows directly from the complete table. The attainment cones above
prove the reverse inclusion; every label also has an archived exact literal-word
witness. Canonical list and scalar membership predicate are compared separately.

RR r=3 is R(B2h), RR r=2 is R(B2), and RF r=5 is K.
Their complete stars and typed exits already exist in the P and H3 packets.
Bind those interfaces here rather than reclassifying them. B2's selected exit
has one edge at n>=4 and four at n=3, retaining the old LAST-c control;
B2h has two edges and K has three. Both orientations of all three old paths
are replayed in every member. IDs 34/35/36 name B2/B2h/K in this composed
registry; this is reuse, not three new complete-star results.

The inherited R5 exit is RR(t+1,1)->R(B2h), followed by its two-edge
reversed H1 suffix to typed C=(y,y,0,0,0). Its length remains exactly three
along this selected route. The bottom y-prefix gives c-coordinate -2;
D3's c-prefix instead gives P0 with c-coordinate -1. A copied D3 step is
refused even if a field-only comparison were tempting.

Six of the 18 image labels have registered complete stars and exits. The
other twelve labels are the four orientations of xx r=3,4, the four of
yx r=3,4, and the four of yc r=2,3. No uniform exit for those twelve is
registered here. That is a certificate-coverage gap, not unproductivity.
Every-direct-child productivity remains unproved on every parameter subcone
by this registry: the still-uncovered RL families occur throughout the cone.
This is not an assertion that no other proof mechanism can apply.

## Inventory and actual nonclosure

| Scope | Complete stars/terminal before | After | Registered exits after |
| --- | --- | --- | --- |
| S41 | 29 | 31 | 31 |
| Y4 image, 18 labels | 14 | 16 | 18 |
| R3/D3 image, 36 labels | 22 | 22 | 22 |
| R5 image, 18 labels | 6 reused | 6 | 6 |

S41 now has **30 nonterminal complete stars plus C**, ten star gaps and ten
exit gaps. R5 gains stars; its existing exit is unchanged. B2/B2h/K are absent
from S41. All 41 candidate and 18 image rows retain separate star/exit flags;
the independent registry compares each row with the native driver.

R5's uniform RR(t+1,1)->R(B2h) leaves S41. Indeed the entire R5 image
has c-coordinate +/-2, while S41 has only 0,+/-1. The image itself is also
not closed: K belongs to it (attained from R5 at t>=2), but its uniform
RF(k+1,0)->L=(y,x,0,3,-4) lies outside it by c-coordinate 3. This is a
uniform escape from a label of the chamber image; K need not be a direct
R5 child in members with t<2. No larger closed carrier is established.
All predecessor cycles and exits remain intact.

The remaining complete-star gap in Y4's image is D5=(x,c,1,-1,0) and its
reversal. Its existing direct RR(d+1,1)->C exit is certified throughout,
and its Y4 LAST/LAST ancestry (A+1,n) is uniform. Classifying D5 is a concrete
next step; its one-step source exit alone does not establish every-child productivity.

## Replay, refusal and non-claims

From kernel/, run `pixi run --locked mojo run -I . tests/test_class_a_boundary_r5_children.mojo`
and the matching `class_a_boundary_r5_children.mojo` driver. From the root,
run `python -m pytest -q tests/test_class_a_boundary_r5_children.py` and
`python oracles/python/class_a_boundary_r5_children.py`. The evidence README
records exact grids, receipts, independent registry reconciliation, dependency
snapshot, source digests and SHA-256 checksums. The 512-refinement independent
exact sign budget refuses on exhaustion. Machine index arithmetic refuses overflow.

Controls refuse invalid chambers/orientations/indices, corrupt field identities,
false t=1 RUN types, copied D3 prefixes, disjoint actual pairs, wrong strict
in-image targets of the same types, incomplete/duplicate stars, altered/truncated
paths, unequal-type zero terminals and missing/duplicate/corrupt registry rows.
Finite replays validate all literal pairs and actual reversed accepted edges;
the table and symbolic cone identities establish the quantified classification.

No new companion exit, all-direct-child productivity, all-edge decreasing rank,
forward closure, all-source cyclic strict-zipper, plus/non-unit/internal-space
transfer, target-aware BH, universal #139, A1-prime/G1, global BH or PSC conclusion.
Preserve 124 governed claims, 34 named Lean proofs and 325 source openings.
