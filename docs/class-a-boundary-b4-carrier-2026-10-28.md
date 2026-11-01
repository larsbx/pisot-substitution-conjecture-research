# B4: complete stars, half-chamber rounding and three-case typed exits

## Scope and inherited hypotheses

Continue #376 at 995331ff2ac8803480923003a8f8ce108434bc87. Preserve its
complete evidence and every predecessor source. Name the next uniform R3 child
B4=(y,x,0,-1,-1). This increment supplies its two complete oriented stars,
a selected typed exit of length at most five, and uniform selected exits for
two companion sources D0 and F4. It does not supply complete stars for those
companions. Independent human review remains pending; exact-head hosted gates
remain required for dependent integration. No governed or formal-source status
changes. The [stop/go](class-a-boundary-b4-stopgo-2026-10-28.md) reuses the
existing three-primary-source actual-overlap/non-unit review and exact half separator.

Keep k,t>=0, n=k+t+3, d=2n-1-k=k+2t+5, A=n+d=2n+t+2 and N=n-1.
Ordered words are x->x y^A x, c->c y^n x, y->x y^N c. All offsets are
full bottom-minus-top integer Parikh triples in the (x,c,y) basis. Actual
zero-based occurrence indices, all three coordinates, actual reversal and the
strict guard -L(bottom child)<s<L(top child) are retained.

Inherited exact quantities are h=1/beta, alpha=beta-(n+2),
a=Lx=2+alpha-h, b=Lc=1+h, Ly=1, z=alpha+h and zeta=alpha-2h.
Use 0<h<1/5, 0<alpha<1, 0<z<1 and zeta>0. The exact earlier separator is

    H=1 iff alpha>1/2 iff t>k or (t=k and k>=2).

Otherwise H=0 and alpha<1/2. Equality is excluded by the earlier polynomial
certificate, not by sampling. The diagonal members k=t=0,1 are low, while
k=t>=2 is high. No decimal root approximations or tile-length independence
assumption enter the argument.

## Ancestry and incidence transport

B4 has physical shift -b-1=-2-h. Its lower source margin is
 a-b-1=zeta>0; its upper margin is 3+h>0. It is R3's actual RUN/FIRST
child (d+2,0), since subtracting top prefix (1,0,d+1) from R3's image
(1,-1,d) gives (0,-1,-1), with actual y/x types. The top index remains a
true RUN because A-(d+2)=n-2>=1. Reverse both indices and negate the full
offset for the other orientation.

For M(p,q,r)=(2p+q+r,q+r,A*p+n*q+N*r),

    M(B4)=(-2,-2,1-2n),
    G=-2a-2b+1-2n=-2beta-1=-2n-5-2alpha.

The canonical Q[t,k] certificate checks beta times the source field element
against the image modulo the characteristic cubic, including
beta*G=-2beta^2-beta. It checks all nine typed prefix formulas and both
orientations before the member replays. The universal strict guard argument
is the following exact integer reduction.

## All nine kinds and literal clipping

Top FIRST/RUN/LAST starts are 0,a+i-1,a+N, with 1<=i<=N. Bottom starts
are 0,a+j-1,a+A, with 1<=j<=A. Top LAST is c and bottom LAST is x.

| Kind | Full typed child | Shift s | Accepted actual indices |
| --- | --- | --- | --- |
| FIRST/FIRST | (x,x,-2,-2,1-2n) | G | none |
| FIRST/RUN | (x,y,-1,-2,j-2n) | j-2n-4-alpha-h | i=0, j=2n+4..min(A,2n+6+H) |
| FIRST/LAST | (x,x,-1,-2,t+3) | t-1-alpha-h | (0,A+1) iff t<=3+H |
| RUN/FIRST | (y,x,-3,-2,2-2n-i) | G-a-i+1 | none |
| RUN/RUN | (y,y,-2,-2,1-2n+j-i) | j-i-2n-5-2alpha | delta=j-i=2n+5+H,2n+6+H; 1<=i<=A-delta |
| RUN/LAST | (y,x,-2,-2,t+4-i) | t-2-2alpha-i | max(1,t-3-H)<=i<=t-1, j=A+1 |
| LAST/FIRST | (c,x,-3,-2,2-3n) | G-a-N | none |
| LAST/RUN | (c,y,-2,-2,j-3n+1) | j-3n-5-2alpha | none |
| LAST/LAST | (c,x,-2,-2,1-k) | -k-5-2alpha | none |

An interval with upper endpoint below its lower endpoint is empty. The
RUN/RUN top upper bound N is automatic: A-delta equals t-3-H or t-4-H,
which is less than N=k+t+2. Every other displayed interval is clipped to
actual word indices; the scalar predicate rejects nonexistent occurrences.

The reductions are reconstructible from these exact inequalities:

* FIRST/FIRST has lower margin G+a=-2n-3-alpha-h<0. RUN/FIRST and
  LAST/FIRST have still smaller lower margins.
* FIRST/RUN gives 2n+3+z<j<2n+6+2alpha. Since 0<z<1 and alpha is
  strictly on one side of 1/2, its integers are precisely 2n+4..2n+6+H,
  then clipped to j<=A.
* FIRST/LAST has lower margin t+1-2h>0. Its upper bound is t<3+2alpha,
  giving exactly t<=3+H.
* RUN/RUN gives 2n+4+2alpha<delta<2n+6+2alpha. Thus the two integer
  strips are 2n+5+H and 2n+6+H. Their cardinalities are
  max(0,t-3-H) and max(0,t-4-H).
* RUN/LAST gives t-3-2alpha<i<t-z. Thus its integers are
  t-3-H..t-1, clipped below at 1. Its upper endpoint is below N.
* LAST/RUN, even at j=A, has shift -k-6-2alpha<-1 and fails its lower
  bound. LAST/LAST has lower margin -k-3-alpha-h<0. No LAST case survives.

Let m=min(3+H,max(0,t-1)). FR and RL each have m occurrences; FL has
one iff t<=3+H. Thus the exact total per orientation is

    2m + [t<=3+H] + max(0,t-3-H) + max(0,t-4-H)
      = max(1,2t-1).

At t=0 and t=1 there is exactly one child, both FIRST/LAST. At t=2,3
there are respectively three and five. At t=4 the low case replaces the
high case's FL child by an RR child, leaving seven in both. At t>=5 the
two half-chambers also have the same 2t-1 count but different index sets.
Dropping the separator because the totals agree would change actual edges.
Reversal exchanges indices and types and negates every coordinate.
Canonical synthesis streams O(t+1) actual indices; it does not enumerate
all O(n^2) literal pairs. The regression independently enumerates those pairs.

## Exact 32-label chamber-wide image

The union consists of these sixteen base labels and their distinct reversals,
for 32 total labels. It is a union over all parameter members, not 32 labels
in every member.

| Event | Base typed labels | Number before reversal |
| --- | --- | --- |
| FR | (x,y,-1,-2,r), r=4..7 | 4 |
| FL | (x,x,-1,-2,r), r=3..7 | 5 |
| RR | (y,y,-2,-2,r), r=6..8 | 3 |
| RL | (y,x,-2,-2,r), r=5..8 | 4 |

Containment follows by inserting the accepted indices into the table. Attainment
uses actual finite members, independently reconstructed by both replays. For
example, FR r=7 occurs in a high member with t>=5; FL r=7 at t=4 in the
high half; RR r=6 at t>=4 in the low half and r=8 at t>=6 in the high
half; RL r=8 at t>=5 in the high half. The probe archives an exact k,t,
orientation,i,j witness for every label. An explicit image list and a fixed
scalar predicate are checked against one another.

## Uniform exits for two companions, without complete stars

Name D0=(x,x,-1,-2,3) and F4=(x,y,-1,-2,4). Both are strictly interior
for every k,t>=0, independently of where B4 reaches them.

D0 has shift -1-z with positive lower margin a-1-z=1-2h>0. Its image is
(-1,1,-d-3), with G=-d-4-zeta. Its actual FIRST/RUN (0,d+3) child is
R(T)=(x,y,0,1,-1), of shift h>0. The bottom index is a true RUN since
A-(d+3)=n-3>=0, including equality at the smallest member. The inherited
T certificate then gives R(T)(2,1)->C. D0 therefore has a uniform two-edge
exit. This does not classify its full star.

F4 has shift -z in (-1,0), with lower margin 1-z>0. Its image is
(0,2,-t-6), with G=-t-4+2h. Its actual FIRST/RUN (0,t+2) child is
R(K)=(x,y,1,2,-5), of shift z-1 in (-1,0). The bottom index is a true
RUN since N-(t+2)=k>=0. Reuse the existing K-to-C suffix in reverse:

    R(K)(0,k+1)->R(L)(n-2,0)->R(H1)(2,1)->C.

Thus F4 has a uniform four-edge exit. It also has no complete-star certificate
in this increment. Both companions' selected transitions and true reversals
are checked symbolically; their inherited suffixes remain pinned and replayed.

## B4's selected exit: t=0, t=1, t>=2

| Face | Actual first edge | Reused suffix | Total edges |
| --- | --- | --- | --- |
| t=0 | B4(0,A+1)->D0 | D0->R(T)->C | 3 |
| t=1 | B4(0,A+1)->R(Dxx)=(x,x,-1,-2,4) | existing four-edge E2/Dxx suffix | 5 |
| t>=2 | B4(0,2n+4)->F4 | F4->R(K)->R(L)->R(H1)->C | 5 |

At t=0/1 the FL shift is respectively -1-z or -z, and the complete guard
above proves strictness. At t>=2, A-(2n+4)=t-2>=0, so the selected FR
index is a real RUN and its child has shift -z. The symbolic certificate
uses the separate constant-t faces and the shifted t>=2 cone. Every path
is checked in both orientations with all actual intermediate types.

The tempting uniform FR(0,2n+4)->F4 is false. At t=0 its bottom index
is A+2, outside the word. At t=1 it is A+1, the actual LAST x; the child
has the same Parikh offset as F4 but is x/x R(Dxx), not x/y F4. A shared
physical shift cannot replace the actual typed target. The proof retains
both cases and reuses Dxx's existing work.

For t<=1 the complete star is a singleton and the selected first edge is that
sole child. Hence every direct B4 child is productive on those two faces.
This statement is not extended to t>=2. No immediate typed C is possible:
all direct targets have c-coordinate -2, or +2 after reversal.

## Separate star and exit inventories, and escape from S41

S41 is unchanged: P3's 37-label image plus X/R(X) and D3/R(D3). Compare
all 41 rows, preserving separate complete-star and uniform-exit interfaces.

| S41 inventory | Before B4 | After B4 |
| --- | --- | --- |
| Registered nonterminal complete stars | 22 | 24 |
| Terminal C | 1 | 1 |
| Unregistered labels | 18 | 16 |
| Registered exits, including C | 21 | 23 |

The T2 orientations retain complete stars without a registered uniform exit.
The registry now also binds the already classified Dxx orientations. Dxx,
D0 and F4 are outside S41 and do not inflate its count.

Among B4's 32 outgoing labels, only the two Dxx orientations have registered
complete stars. Six labels have registered uniform exits: Dxx, D0, F4 and
reversals. The four companion orientations have exits without complete-star
coverage. The remaining 26 outgoing labels lack registered uniform exits.
All 32 image rows are compared individually between native and independent
registries; no star flag is inferred from an exit flag.

Every B4 target is outside S41: its c-coordinate is +/-2, whereas S41 has
only -1,0,1. Since every B4 star is nonempty and B4 belongs to S41, this
is another uniform actual escape, preserving all predecessor escapes and
cycles. The older R3/D3 36-label image now has 20 registered complete stars
and 18 registered exits. Eighteen of those 36 labels still lack registered
uniform exits. In particular all four R3 RUN/FIRST targets now have exits;
its other outgoing kinds still include unresolved targets.

## Evidence, controls and replay

Canonical module kernel/psc/class_a_boundary_b4_children.mojo, with native
driver/regression and .github/workflows/class-a-boundary-b4.yml. Native exact
replay at k=0..7,t=0..6: 56 members, 112 complete-star cells, 336 selected-path
source cells, 33,096 literal pairs, 592 accepted occurrences, 528 B4 path edges
and 672 companion path edges (1,200 total). Both orientations and all 32
image labels are attained. The inherited Mojo environment and lock are used
without changing any vendored module.

Independent literal-word/integer-polynomial/Fraction replay at k=0..12,t=0..8:
117 members, 234 complete-star cells, 702 selected-path source cells,
122,616 pairs, 1,690 accepted occurrences, 1,118 B4 path edges and 1,404
companion path edges (2,522 total). Every actual prefix and reversed accepted
edge is checked. The independent 512-refinement sign budget refuses on exhaustion.
Finite replay validates implementation; the exact guard and shifted-cone path
reductions above supply the uniform quantifiers.

Negative controls retain low diagonal k=t=0,1 and high k=t>=2, the t=4
half-chamber index exchange, t=0's missing proposed uniform index and t=1's
LAST/RUN type error despite identical offsets. They reject corrupt field
identities, bad parameters/orientations/indices, a legal disjoint pair, a wrong
interior in-image target with matching types, changed/truncated paths, false
unequal-type zero terminals and incomplete/duplicate indexed stars. Requesting
a companion's complete star is refused; its selected exit cannot supply one.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_b4_children.mojo
pixi run --locked mojo run -I . class_a_boundary_b4_children.mojo
cd ..
python -m pytest -q tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python oracles/python/class_a_boundary_b4_children.py > /tmp/b4.json
cmp /tmp/b4.json evidence/class-a-boundary-b4-2026-10-28/probe.json
sha256sum -c evidence/class-a-boundary-b4-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-b4-2026-10-28/SHA256SUMS
bash tools/verify_all.sh provenance
```

The evidence README distinguishes local completed checks, formal-tool failures
and still-pending hosted gates. No full-suite success is inferred. Preserve
124 governed claims, 34 named Lean proofs and 325 source openings; independent
human review remains pending.

## Next uniform source and remaining scope

The next uniformly reached unregistered R3 target is
R4=(x,y,1,-1,-2), at actual LAST/RUN (A+1,N). Its shift is zeta-1 in
(-1,0), with lower margin zeta>0. Its complete star and selected exit are
not supplied here. The earlier R3 certificate already verifies this event
throughout the cone, including n=3.

All-source cyclic strict-zipper coverage, plus chambers, target-aware BH,
non-unit internal-space/return-lattice realization, universal BH/#139,
A1-prime, G1 and PSC remain open. This packet proves no all-edge descent,
closed carrier or all-t all-direct-child productivity.
