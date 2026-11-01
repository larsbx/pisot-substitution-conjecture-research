# Every actual Y0 first choice has a typed coincidence completion (minus class A)

**Status:** scoped constructive hand proposition, supported by independently
executable exact-affine transport and physical-margin certificates and a separate
literal-word/Fraction regression. Independent human review and hosted exact-head
acceptance pending. This is **not** a forward-closed carrier, all-later-choice
termination statement, global BH, G1, A1-prime, or PSC proof.

## Domain and predecessor

For integers k,t>=0 put n=k+t+3, d=2n-1-k and A=n+d.
Use exactly x -> x y^A x, c -> c y^n x, y -> x y^(n-1) c.
An oriented overlap label is (top,bottom,dx,dc,dy) with bottom-minus-top
Parikh displacement; children require genuine zero-based ordered occurrences,
exact full Parikh transport and strict physical intersection. Reversal swaps
types, swaps the true occurrence indices and negates the displacement.

The source Y0=(y,y,1,-1,-1) was imported onto main through #412, with a
complete nine-kind outgoing star and exact count 2k+8-[t=0] actual indexed
children per orientation. Here are the **ten** distinct labels in the
*chamber-wide Y0-only outgoing union*, not the 42-label union of all
T/X/Y0 source stars. They do not coexist for every parameter.

| Child | Exact tuple | Exists as Y0 child when |
| --- | --- | --- |
| A3 | (x,x,0,-2,3) | t=0, FF(0,0) |
| A4 | (x,x,0,-2,4) | t=1, FF(0,0) |
| K3 | (y,x,-1,-2,3) | all, RF(t+1,0) |
| K4 | (y,x,-1,-2,4) | t>=1, RF(t,0) |
| K5 | (y,x,-1,-2,5) | t>=2, RF(t-1,0) |
| D2 | (y,y,0,-2,2) | all, RR(t+2,1) |
| D3 | (y,y,0,-2,3) | all, RR(t+1,1) |
| CY | (c,y,0,-2,2) | all, LR(n,k+2) |
| CY3 | (c,y,0,-2,3) | t>=1, LR(n,k+3) |
| CC | (c,c,0,-2,3) | **only t=0**, LL(n,n) |

The original #412 complete-star theorem supplies **all indexed** edges,
including multiplicity, beyond the one displayed witness per label.

## New scoped constructive proposition

For **every** k,t>=0 and every strict, actual indexed
Y0-child edge, its fully typed target has a selected path to the
equal-letter zero-offset state C=(y,y,0,0,0) of length <=5.
Including the arbitrary initial Y0 child, the constructed path has
length **<=6**. The statement holds under true reversal.

The selected paths below are all actual ordered (top,bottom) indices.
Five-tuples, not historical nicknames, determine target identity.
Write RH=(y,x,0,1,-1), H=(x,y,0,1,-1),
H1=(x,y,0,-1,1), J=(y,y,0,2,-2),
Q=(y,x,0,-1,1).

**A3 (t=0; two-edge suffix):**
A3 --(n-1,0)--> RH --(2,1)--> C.

**A4 (t=1; five-edge suffix):**
A4 --(A-2,0)--> (y,x,1,2,-4)
--(t+2,0)--> K5 --(k+1,0)--> (y,x,0,3,-4)
--(0,n-2)--> H1 --(1,2)--> C.
K5 is a legitimate intermediate even though K5 is not a *Y0 first
child* at t=1. No invalid inference about first-child eligibility is made.

**K3 (all; two edges):**
K3 --(0,d+3)--> H --(2,1)--> C.

**K4 (t>=1; two edges):**
K4 --(1,t+5)--> J --(3,1)--> C.

**K5 (t>=2; two or three edges):**
at k=0:
K5 --(0,0)--> (x,x,1,3,-4) --(d+4,0)--> Q --(1,2)--> C;
at k>=1:
K5 --(k,0)--> (y,x,0,3,-3) --(4,1)--> C.

**D2 (all; one or three edges):**
for n>=4: D2 --(1,3)--> C;
at the sole n=3 member (k=t=0):
D2 --(0,2)--> (x,y,1,0,-1)
--(d+1,0)--> Q --(1,2)--> C.
This refuses the false RUN(1,3) transition at n=3,
where bottom ordinal 3 is the actual LAST c.

**D3 (all; two edges):**
D3 --(n-1,0)--> RH --(2,1)--> C.

**CY (all; three edges):**
CY --(0,1)--> (c,y,1,0,-2)
--(t+2,0)--> (y,x,0,-3,3) --(1,4)--> C.
This is one edge shorter than #414's previously recorded
selected CY->Y0->B->RH->C route. Both remain genuine certificates.

**CY3 (t>=1; three or five edges):**
CY3 --(n,0)--> (y,x,1,0,-2)
--(t+3,1)--> E.
For k>=1, E=D2 and D2 --(1,3)--> C (three total).
For k=0, E=CY and the preceding CY three-edge suffix applies
(five total). The k=0 address selects the LAST c rather than a RUN y,
so it is essential not to conflate these two targets.

**CC (t=0 only as a Y0 child; three edges):**
CC --(n+1,2)--> (x,y,1,1,-2)
--(d+2,0)--> Q --(1,2)--> C.
The CC source is separately strictly overlapping for all k,t, but
its Y0 LAST/LAST ancestry is restricted to t=0. The present path
is occurrence-level and does not depend on unmerged PR #416.

## Exact, unbounded verification

The executable checker
oracles/python/class_a_boundary_y0_symbolic_transport.py
partitions k,t>=0 into **six disjoint integer rectangles**:
k=0 or k>=1 crossed with t=0, t=1 or t>=2.
Only actually eligible child labels are considered in each rectangle.
There are exactly **40 label/chamber cases** and **139 selected
occurrence edges** among them. The maximal complete Y0-to-C
path is six edges.

For every selected edge, the checker verifies:
- its real FIRST/RUN/LAST type (including endpoint changes);
- both actual word ordinals by nonnegative affine guards at
  the rectangle corner and every unbounded recession direction;
- each proper-prefix Parikh coordinate;
- the identity w'=Mw+P_bottom-P_top **coefficientwise in Z[k,t]**,
  with M(x,c,y)=(2x+c+y,c+y,A*x+n*c+(n-1)*y).

It never infers a symbolic identity from sampling k,t.

For physical strictness, normalize Ly=1, Lx=2+rho,
Lc=1+h, with h=1/beta and rho=alpha-h. Reuse the existing
exact Perron bounds 0<h<1/5, h<rho, rho+2h<1.
This gives the *open* rational polytope with closure vertices
(h,rho)=(0,0),(0,1),(1/5,1/5),(1/5,3/5).
Every physical strict margin s+L_bottom or L_top-s
is linear in (1,h,rho). Nonnegative values at these four
vertices and a nonzero linear functional imply strict positivity
throughout the open polytope. The independent exact-Fraction
checker verifies **90 strict margins** on **45 oriented**
states (26 base states before reversals), conditional on the
inherited root bounds. No numerical or analytic limit is used.

## Independent literal-word replay and nonclaims

oracles/python/class_a_boundary_y0_every_child.py
checks every actual indexed first choice, every selected
intermediate literal occurrence, each integer Parikh coordinate,
strict rational Perron geometry and true reversed edges
for 117 members (0<=k<=12,0<=t<=8):
234 oriented sources / 50,700 ordered pairs /
**4,654 indexed first-choice edges** /
**12,920 composed path edges**, maximum selected depth six.
It refuses invented ordinals, mutated types, wrong target
offsets and the n=3 and k=0 endpoint confusions.

These finite experiments validate implementations separately
from the all-parameter affine and rational-polytope derivations.
No assertion is made that all *later arbitrary child choices* terminate,
that all cyclic strict-zipper sources reach this carrier, or that the
ten-label image is forward closed. There is no global BH, G1,
A1-prime, plus-chamber, non-unit realization, or PSC promotion.
