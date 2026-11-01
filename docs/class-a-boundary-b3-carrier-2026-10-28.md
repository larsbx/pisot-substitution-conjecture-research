# B3: complete oriented stars, two-edge typed exit and carrier escape

## Scope and hypotheses

Continue #375 at 5143d72eaaf0b79e58b978dcd34e5a2080984c3c, retaining
its complete R3/D3 evidence and all predecessor work. This increment classifies
B3=(y,x,0,-1,0) and its actual reversal. It does not promote governed claims
or change formal sources. Independent human review remains pending; exact-head
hosted predecessor acceptance is still required before dependent integration.
The [stop/go](class-a-boundary-b3-stopgo-2026-10-28.md) reuses the existing
three-primary-source actual-overlap and non-unit hypothesis review.

Integers k,t>=0 give n=k+t+3, d=2n-1-k=k+2t+5, A=n+d and N=n-1.
The ordered words are x->x y^A x, c->c y^n x, y->x y^N c.
Offsets retain all bottom-minus-top integer Parikh coordinates in the (x,c,y)
basis. Occurrences are zero-based; strict intersection means
-L(bottom child)<s<L(top child). Actual reversal transposes types and
occurrence indices and negates all three offset coordinates.

Use the inherited exact identities h=1/beta, alpha=beta-(n+2),
a=Lx=2+alpha-h, b=Lc=1+h, Ly=1. Their certified bounds are
0<h<1/5, 0<alpha<1, alpha+h<1 and zeta=alpha-2h>0.
No decimal root approximation or integer-independence assumption on tile
lengths is introduced. B3 has shift -b. Its lower source margin is a-b>1,
and its upper margin 1+b>0, so it is strictly interior throughout the cone.

## Ancestry, incidence and inflated shift

R3's actual RUN/FIRST child (d+1,0) is B3. The top ordinal is a true RUN
since A-(d+1)=n-1>=2. R3's image (1,-1,d) loses top prefix (1,0,d),
giving (0,-1,0), with actual y/x types. Its reversal has indices (0,d+1).
This ancestry includes n=3 without an endpoint exception.

For M(p,q,r)=(2p+q+r,q+r,A*p+n*q+N*r),
M(B3)=(-1,-1,-n). Its inflated shift is
G=-a-b-n=-beta-1=-n-3-alpha. The canonical certificate verifies both
beta times the source shift and this expression modulo the characteristic
cubic over Q[t,k]. Specifically beta*G=-beta^2-beta. All nine typed
prefix updates and both orientations are checked independently of the
strict-guard reductions below.

Top FIRST/RUN/LAST starts are 0,a+i-1,a+N, with 1<=i<=N.
Bottom starts are 0,a+j-1,a+A, with 1<=j<=A. Top LAST is c;
bottom LAST is x. Losing either distinction changes the typed target.

## Complete nine-kind table

| Kind | Full typed child | Shift s | Accepted actual indices |
| --- | --- | --- | --- |
| FIRST/FIRST | (x,x,-1,-1,-n) | G | none |
| FIRST/RUN | (x,y,0,-1,j-n-1) | j-n-2-h | i=0, j=n+2..n+4 |
| FIRST/LAST | (x,x,0,-1,d) | d-1-h | none |
| RUN/FIRST | (y,x,-2,-1,1-n-i) | G-a-i+1 | none |
| RUN/RUN | (y,y,-1,-1,j-i-n) | j-i-n-3-alpha | j-i=n+3,n+4; 1<=i<=min(N,A-(j-i)) |
| RUN/LAST | (y,x,-1,-1,d-i+1) | d-2-alpha-i | i=N, j=A+1 iff t=0 |
| LAST/FIRST | (c,x,-2,-1,1-2n) | G-a-N | none |
| LAST/RUN | (c,y,-1,-1,j-2n) | j-2n-3-alpha | i=n, j=2n+3..min(2n+4,A) |
| LAST/LAST | (c,x,-1,-1,t+3) | t-alpha | i=n, j=A+1 iff t<=1 |

Here are the exact integer reductions, including the exclusions.

* FIRST/FIRST fails its lower strict bound since G+a=-n-1-h<0.
  RUN/FIRST and LAST/FIRST have still smaller lower margins.
* FIRST/RUN gives n+1+h<j<n+4+alpha. Since 0<h<1 and 0<alpha<1,
  the exact integers are n+2,n+3,n+4. They are all true RUNs because
  A-(n+4)=d-4>=1.
* FIRST/LAST has upper margin a-(d-1-h)=3+alpha-d<0, since d>=5.
* RUN/RUN gives n+2+alpha<j-i<n+4+alpha, hence n+3,n+4.
  For the first strip A-(n+3)-N=t>=0, giving N occurrences. For the second,
  A-(n+4)-N=t-1: it has N-1 occurrences at t=0 and N at t>=1.
  Lower bounds are automatic from i>=1 and the positive deltas.
* RUN/LAST gives d-3-alpha<i<d-h, hence d-3,d-2,d-1 before clipping.
  Since (d-3)-N=t, only t=0,i=N survives. Its shift is 1-alpha in (0,1),
  but the bottom type is x, not the y of a fictitiously extended RR strip.
* LAST/RUN gives 2n+2+alpha<j<2n+4+alpha+h, hence 2n+3,2n+4.
  Since A=2n+t+2, there are zero, one, two true RUNs at t=0, t=1, t>=2.
  At t=0, j=2n+3 is the actual LAST x at A+1. At t=1, j=2n+4 is LAST x.
  The corresponding literal pair can still intersect; it belongs to LAST/LAST
  and must not be called a RUN or assigned a c/y target.
* LAST/LAST has lower margin t-alpha+a=t+2-h>0. Its upper strict bound
  is t<1+alpha+h, which is exactly t<=1 because 0<alpha+h<1.

Thus the per-orientation counts are:

| Parameter face | FR | RR | RL | LR | LL | Total |
| --- | --- | --- | --- | --- | --- | --- |
| t=0 | 3 | 2n-3 | 1 | 0 | 1 | 2n+2 |
| t=1 | 3 | 2n-2 | 0 | 1 | 1 | 2n+3 |
| t>=2 | 3 | 2n-2 | 0 | 2 | 0 | 2n+3 |

Every syntactic kind is covered, and actual reversal exchanges the indices
and transposes the table. Synthesis uses the two O(n) strips and a fixed
number of endpoints; no quadratic search is used by the canonical producer.
The regression deliberately compares it with every literal pair.

## Exact outgoing union and selected exit

The chamber-wide outgoing union consists of these ten base labels and their
20 distinct orientations. It is a union over parameters, not 20 labels in
every member.

| Event | Base labels | Parameter availability |
| --- | --- | --- |
| FR | H1/H2/H3=(x,y,0,-1,r), r=1,2,3 | all k,t |
| RR | P0/P1=(y,y,-1,-1,r), r=3,4 | all k,t |
| RL | (y,x,-1,-1,4) | t=0 only |
| LR | (c,y,-1,-1,3), (c,y,-1,-1,4) | respectively t>=1 and t>=2 |
| LL | (c,x,-1,-1,3), (c,x,-1,-1,4) | respectively t=0 and t=1 |

Containment follows directly from the nine-kind table. FR labels have witnesses
(0,n+r+1), RR labels (1,n+r+1); all are legal on the full cone. The remaining
labels have the exact conditional witnesses in the table, including k=0 on
t=0,1,2. The independent probe archives a literal witness for every orientation.
A fixed scalar predicate and an explicit 20-row list describe the same image.

B3(0,n+2)->H1=(x,y,0,-1,1), then H1(1,2)->C=(y,y,0,0,0).
The first shift is -h in (-1,a); the existing E/H certificate supplies the
second actual typed edge. The first ordinal n+2 stays strictly in the bottom
RUN even at k=t=0, where A=8. Reversing each edge gives the same two-edge
bound. No immediate typed C is possible: every outgoing label has nonzero
c-coordinate. The alternative uniform RR(1,n+4)->P0 is retained and checked,
but the shorter H1 path needs no k split and no P0 suffix.

The ten oriented H1/H2/H3/P0/P1 targets have registered complete stars and
uniform exits. The other ten oriented targets have neither interface registered
here. This is a proof-coverage statement, not evidence that those targets are
unproductive. All-direct-child productivity remains unproved.

## Reconcile S41 and the older 36-label image

Preserve S41 exactly as defined by #375: P3's 37-label image, X/R(X),
D3/R(D3). Its 41 rows are compared individually between canonical driver and
independent oracle, retaining separate star and exit flags.

| S41 inventory | Before B3 | After B3 |
| --- | --- | --- |
| Registered nonterminal complete stars | 20 | 22 |
| Terminal C | 1 | 1 |
| Unregistered labels | 20 | 18 |
| Registered exits, including C | 19 | 21 |

The T2 orientations retain classified stars without a registered uniform exit.
The new registry also binds the existing E/H H1/H2 interfaces for outgoing
coverage; neither family is a member of S41, so they do not inflate its count.
This registry does not assert that all other repository methods are inapplicable
to an unregistered label.

B3 belongs to S41, while H1 and its reversal do not. Hence the selected
FIRST/RUN edge is another uniform actual escape from S41. This preserves
both prior R3->D3 and D3->P0 escapes rather than silently closing a candidate.
Within the older R3/D3 36-label outgoing union, classifying B3/R(B3) raises
registered stars from 16 to 18 and registered uniform exits from 14 to 16.
Twenty of those 36 outgoing labels still lack a registered uniform exit.

## Evidence and replay

Canonical module: kernel/psc/class_a_boundary_b3_children.mojo, with native
driver and regression; dedicated .github/workflows/class-a-boundary-b3.yml.
Locked local Mojo 1.1.0.dev2026090805: k=0..7,t=0..6 gives 56 members,
112 oriented source cells, 33,096 literal pairs, 2,448 accepted occurrences
and 224 selected path edges. Every accepted/rejected pair is compared with
full Parikh transport and strict exact Perron-field geometry. Both orientations
and all 20 targets are attained. The universal guard proof is the integer
reduction above; finite replay validates its implementation.

Independent literal-word/integer-polynomial/Fraction oracle: k=0..12,t=0..8
gives 117 members, 234 source cells, 122,616 pairs, 6,760 accepted occurrences
and 468 selected path edges. It reconstructs every literal prefix, checks the
affine geometric recurrence, every reversed accepted edge, exact image equality,
actual R3 ancestry, endpoint types, selected path and row-by-row source registry.
The inherited sign budget is 512 refinements and refuses on exhaustion.

Negative controls reject corrupt field identities, bad parameters/orientations
and unavailable indices; the legal but disjoint FR(0,n+1); an interior H2
substituted for intended H1 despite matching types and image membership;
t=0's real LAST ordinal supplied as RUN; truncated/changed paths, false
unequal-type zero terminals and duplicate/incomplete indexed stars. The t=0
clipped second RR endpoint is a real y/x edge, not a disjoint pair; the tests
retain that actual type rather than incorrectly refusing the entire event.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_b3_children.mojo
pixi run --locked mojo run -I . class_a_boundary_b3_children.mojo
cd ..
python -m pytest -q tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python oracles/python/class_a_boundary_b3_children.py > /tmp/b3.json
cmp /tmp/b3.json evidence/class-a-boundary-b3-2026-10-28/probe.json
sha256sum -c evidence/class-a-boundary-b3-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-b3-2026-10-28/SHA256SUMS
bash tools/verify_all.sh provenance
```

Receipts and truthful formal-tool outcomes are recorded in the evidence README.
No full native/Python-suite or fresh hosted pass is inferred from scoped results.
No Lean/TLA sources or governed statuses change: preserve 124 claims,
34 named Lean proofs and 325 source openings. Independent human review pending.

## Remaining scope and next uniform source

R3's next still-unregistered uniform child is (y,x,0,-1,-1) at (d+2,0).
Its shift is -b-1, and its lower margin a-b-1=zeta>0. The top occurrence
is a real RUN because A-(d+2)=n-2>=1. This is a verified next source,
not a proposed classification or exit certificate in this packet.

All-source cyclic strict-zipper coverage, plus chambers, target-aware BH,
non-unit internal-space/return-lattice realization, universal BH/#139,
A1-prime, G1 and PSC remain open. No all-edge descent, closed carrier or
global productivity conclusion follows from B3's selected two-edge path.
