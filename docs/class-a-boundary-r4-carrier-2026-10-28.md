# R4: complete stars, short typed exits and separate companion coverage

## Scope and inherited hypotheses

Continue #377 at 318a866ad5e40dfe1ac841ad060f68438bc40c8a, preserving all
predecessor sources and evidence. Classify R4=(x,y,1,-1,-2) and its actual
reversal throughout the minus class-A boundary chamber. Supply five companion
uniform exits without claiming their complete stars. Independent human review
remains pending; exact-head hosted gates remain required for integration in
stack order. No governed or formal-source status changes. The
[stop/go](class-a-boundary-r4-stopgo-2026-10-28.md) reuses the existing
three-primary-source actual/every-overlap and non-unit review.

Keep k,t>=0, n=k+t+3, d=2n-1-k=k+2t+5, A=n+d=2n+t+2 and N=n-1.
The actual ordered words are x->x y^A x, c->c y^n x, y->x y^N c.
Offsets retain all bottom-minus-top integer Parikh coordinates in the (x,c,y)
basis. Indices are zero-based. Strict intersection means
-L(bottom child)<s<L(top child). Reversal transposes types and indices and
negates all three coordinates.

Use inherited h=1/beta, alpha=beta-(n+2), a=Lx=2+alpha-h,
b=Lc=1+h, Ly=1, z=alpha+h and zeta=alpha-2h. The certified bounds are
0<h<1/5, 0<alpha<1, zeta>0 and 0<alpha+2h<1; in particular 0<z<1.
The last upper bound is the existing T_m polynomial-remainder certificate,
not an assumption inferred from samples. No decimal root approximation or
tile-length independence assumption enters a decision.

## Actual ancestry and field transport

R4 has physical shift a-b-2=zeta-1 in (-1,0), with lower margin zeta>0.
It is R3's uniform actual LAST/RUN child (A+1,N): subtract top prefix
(1,0,A) and add bottom prefix (1,0,N-1) to R3's image (1,-1,d), giving
(1,-1,-2), with actual x/y types. The bottom N=n-1>=2 is a genuine RUN,
including n=3. The reversed edge has indices (N,A+1).

For M(p,q,r)=(2p+q+r,q+r,A*p+n*q+N*r),

    M(R4)=(-1,-3,1-k),
    G=-a-3b+1-k=-k-4-alpha-2h.

The canonical certificate checks every source's full incidence image and
beta times its field element modulo the characteristic cubic over Q[t,k].
For R4, beta*G=-beta^2+(n-k-2)*beta-2. The generic incidence computation
and separately supplied expected image are compared, rather than trusting
only a selected target's physical shift.

## All nine kinds and exact strict guards

Top FIRST/RUN/LAST starts are 0,a+i-1,a+A with 1<=i<=A; bottom starts
are 0,a+j-1,a+N with 1<=j<=N. Top LAST is x, bottom LAST is c.

| Kind | Full typed child | Shift s | Accepted actual indices |
| --- | --- | --- | --- |
| FIRST/FIRST | (x,x,-1,-3,1-k) | G | none |
| FIRST/RUN | (x,y,0,-3,j-k) | j-k-3-3h | i=0, j=k+3..min(N,k+5) |
| FIRST/LAST | (x,c,0,-3,t+3) | t-3h | (0,n) iff t<=2 |
| RUN/FIRST | (y,x,-2,-3,2-k-i) | G-a-i+1 | none |
| RUN/RUN | (y,y,-1,-3,1-k+j-i) | j-i-k-4-alpha-2h | j-i=k+4,k+5; 1<=i<=N-(j-i) |
| RUN/LAST | (y,c,-1,-3,t+4-i) | t-1-alpha-2h-i | max(1,t-2)<=i<=t-1, j=n |
| LAST/FIRST | (x,x,-2,-3,1-k-A) | G-a-A | none |
| LAST/RUN | (x,y,-1,-3,j-k-A) | G+j-1-A | none |
| LAST/LAST | (x,c,-1,-3,-k-d) | G+N-A | none |

Every interval is clipped to actual word indices; an empty interval contributes
no occurrence. For RR and RL the top bound A is automatic, since their maximum
indices are at most t-2 and t-1, while A=2k+3t+8.

The exact integer rounding and exclusions are:

* FF has lower margin G+a=-k-2-3h<0. RF and LF have still smaller
  lower margins, so all three are disjoint.
* FR gives k+2+3h<j<k+5+alpha+2h. Since 0<3h<1 and
  0<alpha+2h<1, the exact integer range is k+3..k+5, clipped to N.
* FL has lower margin t+1-2h>0. Its upper bound t<2+alpha+2h gives
  precisely t<=2.
* RR gives k+3+alpha+2h<j-i<k+5+alpha+2h. Thus the two deltas are
  k+4,k+5. Their occurrence counts are max(0,t-2), max(0,t-3).
* RL gives t-2-alpha-2h<i<t-z. The exact integers are t-2,t-1,
  clipped below at 1; its count is min(2,max(0,t-1)).
* LR has maximum shift at j=N equal to G+N-1-A=G-d-2, below -1.
  LL has lower margin G+N-A+b=G-d+h<0. These are not omitted
  syntactic candidates; their strict guards fail.

Therefore the per-orientation count is

    min(3,t) + [t<=2] + max(0,t-2) + max(0,t-3)
      + min(2,max(0,t-1)) = max(1,2t).

At t=0 there is one FL child. At t=1 there are two children (FR and FL).
At t=2 there are four (two FR, one FL, one RL). For t>=3 the count is
2t. These are occurrence counts, not distinct-label counts. The same proof
holds under actual reversal. Canonical synthesis streams O(t+1) actual
indices; the regression compares it with all O(n^2) literal pairs.

## Exact 20-label outgoing image

The chamber-wide union consists of these ten base labels and their distinct
reversals, giving twenty labels. It is a union over parameters, not twenty
labels in each member.

| Event | Base labels | Availability |
| --- | --- | --- |
| FR | D4=(x,y,0,-3,3), R(L)=(x,y,0,-3,4), G5=(x,y,0,-3,5) | respectively t>=1, t>=2, t>=3 |
| FL | E4=(x,c,0,-3,3), E5=(x,c,0,-3,4), (x,c,0,-3,5) | respectively t=0, t=1, t=2 |
| RR | (y,y,-1,-3,5), (y,y,-1,-3,6) | respectively t>=3, t>=4 |
| RL | (y,c,-1,-3,5), (y,c,-1,-3,6) | respectively t>=2, t>=3 |

Containment follows by inserting the complete strict index ranges. Each label
is attained by an actual member with k=0 and a listed t, then by actual
reversal. The probe archives its exact k,t,orientation,i,j witness. The fixed
scalar image predicate and explicit 20-row image list are checked for agreement.

## Five companion uniform exits, without complete stars

Their source images and strict source shifts are:

| Source | M offset | Physical shift | Selected exit bound |
| --- | --- | --- | --- |
| E4=(x,c,0,-3,3) | (0,0,-3) | -3h | 2 |
| D4=(x,y,0,-3,3) | (0,0,-3) | -3h | 7, or 3 at n>=4 |
| Y4=(x,y,1,0,-1) | (1,-1,d+1) | a-1 | 2 |
| E5=(x,c,0,-3,4) | (1,1,n-4) | 1-3h | 3 |
| G5=(x,y,0,-3,5) | (2,2,2n-5) | 2-3h | 5 |

All sources are strictly interior. For E4/D4, 3h<1 supplies the lower
margin even with bottom y; E4's bottom c is longer. For Y4 the upper margin
is 1. For E5 the shift lies in (0,1). For G5 the upper margin is alpha+2h>0.
None of their complete outgoing stars is supplied or registered here.

Uniform actual transitions, followed by existing typed suffixes, are:

* E4(0,3)->R(T)=(x,y,0,1,-1), then R(T)(2,1)->C. The bottom parent
  is c, so its RUN prefix is (0,1,2), not (1,0,2). The child shift is h.
  The actual ordinal 3 is a RUN since n>=3.
* Y4(d+1,0)->T=(y,x,0,-1,1), then T(1,2)->C. The first child has
  shift -h and d+1<=A follows from n>=3.
* E5(n,1)->B2h=(y,y,0,2,-3), then the existing B2h(0,N)->H1(1,2)->C.
  The first child shift is -1+2h. Both are true RUNs. The actual c-prefix
  changes the first two Parikh coordinates: this is B2h, not R(P0).
* G5(2n,0)->J=(y,x,1,2,-4), then the existing J->K->L->H1->C suffix.
  Its first child shift is z=alpha+h in (0,1), and 2n<=A.

For D4 at n>=4, D4(0,3)->Y4 and the preceding Y4 suffix gives three
edges. Its child shift is a-1. The bottom 3 is a RUN exactly when n>=4;
the symbolic certificate uses the union of shifted k and t cones covering
that domain.

At the sole n=3 member k=t=0, the same bottom ordinal 3 is LAST c.
The actual child is (x,c,1,0,-1), of shift a-1 and **still strictly interior**.
It is not Y4, whose bottom type is y. Retain this real edge and reject the
false uniform RUN/type assertion. D4 instead has the following seven-edge path:

    D4(0,2)->(x,y,1,0,-2)
       (0,0)->(x,x,0,-2,4)
       (7,0)->J->K->L->H1->C.

The first intermediate has shift rho=alpha-h>0 with upper margin 2. The
second has shift 2-2h with upper margin alpha+h>0. Its RF(2n+1,0)->J
edge is the same incidence/strict-guard specialization used by H4, with the
actual bottom FIRST x. The suffix is the existing J path. All seven literal
edges and their true reversals are checked; the constant member is not
extrapolated to other parameters. This closes D4's uniform selected exit while
leaving its complete star unclassified.

## R4 selected paths and the t<=1 all-child result

| Face | Actual first edge | Suffix | Total edges |
| --- | --- | --- | --- |
| t=0 | R4(0,n)->E4 | E4->R(T)->C | 3 |
| t=1 | R4(0,k+3)->D4 | n>=4 D4->Y4->T->C | 4 |
| t>=2 | R4(0,k+4)->R(L) | existing R(L)(n-2,0)->R(H1)(2,1)->C | 3 |

FL at t=0 has shift -3h. FR at t=1 has shift -3h. FR at t>=2 has
shift 1-3h, and N-(k+4)=t-2>=0 proves that its ordinal is a true RUN.
The source transition certificates use constant t=0/1 faces and the shifted
t>=2 cone. Every complete path retains the intended indices and all typed
intermediates under reversal.

A proposed uniform R4(0,k+4)->R(L) is false: at t=0 this index is n+1,
outside the bottom word; at t=1 it is n, the actual LAST c, producing E5
with the same offset as R(L) but different types. That E5 edge is real and
productive by its separate three-edge suffix, not discarded.

At t=0 the sole direct child is E4; at t=1 the two direct children are
D4 and E5. All have uniform typed exits, so every direct R4 child is
productive on t<=1. For t>=2 this packet proves selected-source reachability,
not all-direct-child productivity. Every direct target has c-coordinate -3
(or +3 after reversal). The only equal-type targets are RR, with shifts
-alpha-2h and 1-alpha-2h, both nonzero by 0<alpha+2h<1. Thus there
is no immediate typed coincidence, without a tile-length independence premise.

## Coverage reconciliation: exit flags do not supply stars

S41 remains P3's 37-label image plus X/R(X) and D3/R(D3). Compare all
41 rows with separate complete-star and uniform-exit interfaces.

| S41 inventory | Before R4 | After R4 |
| --- | --- | --- |
| Registered nonterminal complete stars | 24 | 26 |
| Terminal C | 1 | 1 |
| Unregistered complete-star labels | 16 | 14 |
| Registered uniform exits, including C | 23 | 27 |

The new R4 orientations add both kinds of coverage. Y4/R(Y4) belong to S41
and now have exits but still no complete-star interface. Conversely T2/R(T2)
retain complete stars without a registered uniform exit. The equal final star
and exit totals (27 including C) therefore do not mean the covered label sets
are identical. Every row, not just each total, is checked.

In R4's 20-label image, only L/R(L) have registered complete stars. Ten
labels have registered uniform exits: L, E4, D4, E5, G5 and their reversals.
The other ten outgoing labels still lack registered exits. Uniform companion
paths are not turned into complete-star claims. The existing complete L
interface is newly bound for this inventory but its proof is reused.

All twenty direct targets lie outside S41, whose c-coordinates are only
-1,0,1. Because R4 belongs to S41 and every R4 star is nonempty, this
supplies another uniform actual escape. Preserve all older escapes and cycles.
The older R3/D3 36-label image now has 22 registered complete stars and
20 registered uniform exits; sixteen labels still lack registered exits.

## Evidence, controls and replay

Canonical module kernel/psc/class_a_boundary_r4_children.mojo, matching native
driver/regression and dedicated .github/workflows/class-a-boundary-r4.yml.
Native k=0..7,t=0..6 replay: 56 members, 112 complete-star cells,
672 selected-path source cells, 33,096 literal pairs, 688 accepted occurrences,
352 R4 path edges and 1,688 companion path edges (2,040 total).
All 20 image labels and both orientations are attained; every literal pair
is compared with full Parikh transport and strict exact Perron-field geometry.

Independent literal-word/integer-polynomial/Fraction replay at k=0..12,t=0..8:
117 members, 234 complete-star cells, 1,404 selected-path source cells,
122,616 pairs, 1,898 accepted occurrences, 728 R4 path edges and 3,518
companion edges (4,246 total). The fixed 512-refinement sign budget refuses
on exhaustion. Finite replays validate implementation; the universal guards,
source bounds and shifted-cone/path reductions above supply the quantifiers.

Negative controls preserve t=0/1's false uniform R(L) indices, D4's true
n=3 LAST c edge and correct E5 c-prefix. They refuse corrupted field
identities, invalid parameters/orientations/indices, a legal disjoint pair,
a wrong interior in-image target with matching types, omitted/duplicate/altered
native registry rows, changed/truncated paths, false unequal-type zero terminals
and incomplete/duplicate stars. Companion complete-star requests are refused.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_r4_children.mojo
pixi run --locked mojo run -I . class_a_boundary_r4_children.mojo
cd ..
python -m pytest -q tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python oracles/python/class_a_boundary_r4_children.py > /tmp/r4.json
cmp /tmp/r4.json evidence/class-a-boundary-r4-2026-10-28/probe.json
sha256sum -c evidence/class-a-boundary-r4-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-r4-2026-10-28/SHA256SUMS
bash tools/verify_all.sh provenance
```

The evidence README distinguishes completed local checks, formal-tool failures
and pending hosted acceptance. No full-suite success is inferred. Preserve
124 governed claims, 34 named Lean proofs and 325 source openings; independent
human review remains pending.

## Next star and remaining scope

Y4=(x,y,1,0,-1) is a concrete next complete-star gap in S41. Its uniform
two-edge typed exit is now certified, but its full outgoing star is unclassified.
For t>=1 it is reached through R4(0,k+3)->D4(0,3)->Y4; this ancestry
is not asserted at t=0. Its own strict source geometry and exit are uniform
throughout k,t>=0.

All-source cyclic strict-zipper coverage, plus chambers, target-aware BH,
non-unit internal-space/return-lattice realization, universal BH/#139,
A1-prime, G1 and PSC remain open. No all-edge descent, closed carrier,
complete companion stars or all-t all-direct-child productivity is concluded.
