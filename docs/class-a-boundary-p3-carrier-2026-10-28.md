# P3: complete stars and two-step typed-coincidence exits

## Hypotheses and exact scope

Continue #365 at P3=(x,y,1,3,-4). Integers k,t>=0,
n=k+t+3, d=2n-1-k, A=n+d, N=n-1; ordered images are
x->x y^A x, c->c y^n x, y->x y^N c. All offsets are full
bottom-minus-top Parikh vectors. Reversal swaps types and actual indices
and negates all three coordinates. Only strict physical intersection counts.
The [stop/go](class-a-boundary-p3-stopgo-2026-10-28.md) retains the inherited
three-source review and the global/non-unit hypothesis boundaries.

Normalize Ly=1, h=1/beta, alpha=beta-(n+2), rho=alpha-h,
a=Lx=2+rho, b=Lc=1+h, w=alpha+2h, zeta=alpha-2h.
The inherited exact field bounds give 0<h<1/5, 0<rho,w<1, 2<a<3.
The cubic identity beta^2*zeta=(t+1)*beta-2 gives zeta>0 because
beta>n+2>=5; zeta<rho<1. No new parameter sign split is needed.

The three base sources and their real reversals give six oriented stars:

| Local name | Full label | Physical shift | Incidence image | Inflated shift G |
| --- | --- | --- | --- | --- |
| P3 | (x,y,1,3,-4) | 1+w | (1,-1,d+4) | d+5+zeta |
| T | (y,x,0,-1,1) | -h | (0,0,-1) | -1 |
| U | (x,x,0,-1,1) | -h | (0,0,-1) | -1 |

T and U are local names for the full displayed labels. P3 is interior:
a-(1+w)=1-3h>0. Both auxiliary sources are interior since h<a.
P3 is E3=(x,x,-1,0,3)'s actual child (A+1,A-k-1) throughout the cone,
including k=t=0. The prefix certificate proves both word bounds.

## Complete nine-kind classification

A FIRST prefix is 0; RUN i prefix is (1,0,i-1), with physical length a+i-1;
LAST R+1 prefix is (1,0,R), physical length a+R.
LAST has type c for parent y, otherwise x. For each actual child pair demand
-L(bottom child)<G+prefix_bottom-prefix_top<L(top child).
All RUN indices below are clipped to the true word. Empty strips contribute
nothing. Reverse by transposing indices and negating full typed labels.

| Kind | P3: top A, bottom N | T: top N, bottom A | U: both A |
| --- | --- | --- | --- |
| FIRST/FIRST | none | (0,0) | (0,0) |
| FIRST/RUN | none | (0,1) | (0,1) |
| FIRST/LAST | none | none | none |
| RUN/FIRST | i=d+3..min(A,d+6), j=0 | none | none |
| RUN/RUN | i-j=d+5,d+6 | j=i+1, i=1..N | j=i+1, i=1..A-1 |
| RUN/LAST | none | none | (A,A+1) |
| LAST/FIRST | (A+1,0) iff n<=5 | none | none |
| LAST/RUN | (A+1,j), j=max(1,n-5)..n-2 | (n,n+1),(n,n+2) | none |
| LAST/LAST | none | none | (A+1,A+1) |

For P3 RUN/RUN impose 1<=j<=min(N,A-delta), delta=i-j.
Here are the reductions for every included and excluded kind.

* P3 RUN/FIRST has shift d+4-h-i. The two strict inequalities give
  d+3<=i<=d+6, using 0<zeta<1, then clip i<=A.
  RUN/RUN shift is d+5+zeta+j-i, giving precisely the two diagonals.
  LAST/FIRST shift is 3-n-h; its lower margin is 5-n+zeta, positive
  exactly at n<=5, and its upper guard is automatic. LAST/RUN shift is
  4-n+zeta+j; lower guard gives j>=n-5 and upper guard gives
  j<n-2+h, hence j<=n-2. FIRST/FIRST exceeds a since G-a=d+3-h>0;
  FIRST/RUN and FIRST/LAST increase it. RUN/LAST is at least
  G+N-A=4+zeta>1. LAST/LAST is 4+zeta>a. These exclude all other kinds.
* T/U FIRST/FIRST has shift -1 and is an x/x interior child.
  FIRST/RUN has shift a+j-2; only j=1 is below a.
  FIRST/LAST has shift a+A-1>a. RUN/FIRST has shift -a-i<-a.
  RUN/RUN has integral shift j-i-1; strict y/y overlap forces j=i+1.
  RUN/LAST has shift A-i, forcing i=A: unavailable for T, accepted for U.
  LAST/FIRST has shift -1-a-R<-a. LAST/RUN has shift j-R-2:
  for T, -1<j-R-2<b=1+h gives j=R+2,R+3; both are true bottom
  runs since A>=n+2. For U, j<=A=R makes the lower guard impossible.
  LAST/LAST has shift A-R-1: d>b for T, and -1 inside x/x for U.

The exact counts per orientation are **2n-3, n+3, A+3** respectively.
For P3 the four contributions are min(4,n-2),
max(0,n-5)+max(0,n-6), one iff n<=5, and min(4,n-2).
Checking n=3,4,5 and n>=6 gives 2n-3, including all clipped endpoints.
Synthesis emits only these O(n+d) strips/endpoints; it never scans the
quadratic word-pair rectangle in production. The exhaustive rectangle is
used by the independent finite regression.

## Full transport and the 37-label image

Use M(x,c,y)=(2x+c+y,c+y,A*x+n*c+N*y), then add the actual
bottom prefix minus top prefix. The canonical Q[t,k] check proves every kind
on affine index bases 1,2 and actual last prefixes, in both orientations.
Clearing the positive denominator beta uses beta*a=beta^2-n*beta-1,
beta*b=beta+1. The field reductions are
beta*G(P3)=beta^2+(d-n+3)*beta-2 and beta*G(T)=beta*G(U)=-beta.
The exact zeta identity is independently checked modulo the cubic.

| Source | Complete base target labels; r is the last coordinate |
| --- | --- |
| P3 | (y,x,0,-1,r), r=-1..2; (y,y,1,-1,r), r=-2,-1; (x,x,0,-1,r), r=-1..1; (x,y,1,-1,r), r=-2..1 |
| T | (x,x,0,0,-1); (x,y,1,0,-1); C=(y,y,0,0,0); (c,y,0,0,r), r=0,1 |
| U | (x,x,0,0,-1); (x,y,1,0,-1); C; (y,x,0,0,0) |

P3 contributes 13 base labels and 13 disjoint reversals. The auxiliary
sources contribute 11 labels after reversal, with C counted once: **37**
labels in the chamber-wide union, not in each member. Polynomial transport
and the guards prove containment; archived actual k,t,i,j witnesses attain
every label. This separates universal containment from finite attainment.
Zero-offset y/x and c/y labels remain valid overlaps and are not typed C.

## Constructive typed exits and the n=3 endpoint

| Source | Actual selected edges | Length |
| --- | --- | --- |
| P3, n>=4 | (d+4,0)->T, (1,2)->C | 2 |
| P3, n=3 (k=t=0) | (A+1,0)->U, (1,2)->C | 2 |
| T or U | (1,2)->C | 1 |

For n>=4, d+4<=A, so the first edge is RUN/FIRST. Its shift is -h,
strictly interior, and its full transport is T. The symbolic word-bound
certificate covers n>=4 by the union k=k'+1 or t=t'+1, shifting n,d
appropriately on each cone. At n=3, d+4=A+1 is the actual LAST x,
not a RUN y: its target is U, with the same offset but different types.
The constant n=3 prefix calculation is checked separately. Both T and U
inflate to offset (0,0,-1); their actual RUN/RUN (1,2) adds (0,0,1),
ending at typed y/y zero. Reversal transposes every step, including terminal
(2,1). No arbitrary child choices or all-edge rank is inferred.

## Evidence, controls and replay

Canonical kernel `kernel/psc/class_a_boundary_p3_children.mojo`, matching
driver and regression:

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_p3_children.mojo
pixi run --locked mojo run -I . class_a_boundary_p3_children.mojo
```

Local locked Mojo 1.1.0.dev2026090805: 56 members (k=0..7,t=0..6),
148,288 ordered pairs, 6,216 accepted occurrences, 448 selected path edges.
Independent literal-word/integer-polynomial/Fraction oracle: 117 members
(k=0..12,t=0..8), 702 source cells, 542,880 pairs, 17,316 accepted,
936 selected path edges. Both attain all 37 labels and check actual E3
ancestry, exact full transport, strict geometry, and all reversed accepted
edges. A 512-refinement oracle sign budget refuses inconclusively on exhaustion.

```sh
python -m pytest -q tests/test_class_a_boundary_p3_children.py
python oracles/python/class_a_boundary_p3_children.py > /tmp/p3-children.json
cmp /tmp/p3-children.json evidence/class-a-boundary-p3-2026-10-28/probe.json
```

Negative controls: the legal P3 RUN/FIRST (d+2,0) has the same child types
as its accepted neighbour but is disjoint. The n=3 index d+4 exists, yet
has type LAST x: the interior T target with the right offset is refused.
Also refuse nonexistent ordinals, bad orientation IDs, duplicate indexed
synthesis, corrupted field identities, changed intermediate labels and
unequal-type zero-offset terminals. Preserve the real U(A,A+1) y/x zero
edge as the latter control.

Receipts and source digests are archived under
`evidence/class-a-boundary-p3-2026-10-28/`; the dedicated workflow is
`.github/workflows/class-a-boundary-p3.yml`. Local TLA, Python and provenance
results are recorded there. The local Lean launcher fails before compilation;
no Lean proof pass is credited. Fresh exact-head hosted gates remain required
before integration. Independent human review pending. No formal source,
governed claim status or named proof is added or promoted.

The 37-label image is not proved forward closed, and not every P3 child is
proved productive. The next explicit unclassified source is
Q3=(x,y,1,-1,1), P3's actual LAST/RUN child (A+1,n-2) throughout the cone.
Its shift is 2+zeta, with upper margin h>0. All-source cyclic strict-zipper,
plus chambers, target-aware BH, non-unit internal-space/return-lattice
realization, universal BH/#139, A1-prime, G1 and PSC remain open.
