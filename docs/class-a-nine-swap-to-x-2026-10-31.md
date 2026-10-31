# Nine swapped-patch overlap seeds reach X uniformly in minus class A

**Status:** new narrowly scoped **all-parameter arithmetic path certificate**
with actual ordered occurrences, typed full-Parikh targets and strict physical
margins, plus an independent finite literal-word/Fraction replay.
Not an all-descendant, all-seed strict-zipper boundary-hitting theorem,
not a complete literature overlap covering argument, and not PSC.
Independent human review and exact-head hosted acceptance remain pending.

## Correct object and substitution parameters

For all integers k,t>=0, write n=k+t+3, d=k+2t+5, A=n+d and
use exactly x->x y^A x, c->c y^n x, y->x y^(n-1) c.
A vertex is an oriented state (top,bottom,dx,dc,dy) with full
**bottom-minus-top** integer Parikh offset. A child needs genuine
zero-based ordered letter occurrences and *strict* physical intersection.

For each unordered pair of distinct letters a<b among (x,c),(x,y),(c,y),
take aligned two-tile patches **ab** (top) and **ba** (bottom), and
enumerate their four ordered tile pairs. The inherited exact
positive-length bounds give Lx=2+rho>Lc=1+h>Ly=1.
Exactly three of each pair's four raw tile contacts are strict
overlaps: nine in total. The other contact is (b,b) shifted by -La,
which lies outside the strict interval because La>Lb.
No invented seeds or reversed-word identifications are introduced.

The nine actual oriented strict sources are:

| Seed | Canonical tuple |
| --- | --- |
| S0 | (x,c,0,0,0) |
| S1 | (x,x,0,1,0) |
| S2 | (c,x,-1,1,0) |
| S3 | (x,y,0,0,0) |
| S4 | (x,x,0,0,1) |
| S5 | (y,x,-1,0,1) |
| S6 | (c,y,0,0,0) |
| S7 | (c,c,0,0,1) |
| S8 | (y,c,0,-1,1) |

Their true reversed orientations are also checked separately.

## A universal X-hub route for each initial seed

Write X=(x,x,1,0,-1), the existing classified W/X state,
and abbreviate these actual intermediates:
P=(x,y,0,1,0), Z=(y,x,0,1,-1),
D=(c,y,0,0,1), E=(c,y,0,1,-1),
F=(c,x,0,0,1), G=(y,c,0,0,0),
H=(c,x,0,0,0), Q3=(x,y,1,-1,1),
L=(x,c,1,0,-1), I=(x,x,0,0,1).

Common certified three-edge suffix:

    S1=(x,x,0,1,0)
      --(n+2,0)--> Z
      --(n,n)----> D
      --(n+1,0)--> X.

Another branch enters through P:

    P --(n+2,0)--> Z --(n,n)--> D --(n+1,0)--> X.

The complete nine selected paths to X are:

| Seed | Actual selected first step(s) before shared suffix | Total |
| --- | --- | ---: |
| S0 | (0,1)->P; then P suffix | 4 |
| S1 | common three-edge S1 suffix | 3 |
| S2 | (0,d)->E; E(0,0)->F; F(n+1,0)->X | 3 |
| S3 | (n,n)->G; G(0,1)->P; then P suffix | 5 |
| S4 | (n+1,0)->Z; then Z(n,n)->D(n+1,0)->X | 3 |
| S5 | (0,d+2)->P; then P suffix | 4 |
| S6 | (0,0)->H; H(n+1,n+2)->Q3; Q3(A+1,0)->X | 3 |
| S7 | (n+1,0)->L; L(A+1,n+1)->I; then S4 suffix | 5 |
| S8 | (0,2)->P; then P suffix | 4 |

All indices are true FIRST/RUN/LAST occurrences for their
**actual source word types**, over the entire unbounded k,t cone.
In particular the n-th occurrence in Z's y image is the
**LAST c**, not RUN y; similarly n+1 is the LAST x of
a c image when selected. The typed targets explicitly preserve
these endpoint distinctions.

The existing mainline X exit

    X --(d+1,0)--> Q=(y,x,0,-1,1) --(1,2)--> C=(y,y,0,0,0)

has two edges. Hence for each of the nine literal swapped-patch
overlap sources, *some* strict typed-coincidence path has at
most **seven** edges for every k,t>=0. This is **source-only
existential reachability**, not an assertion about every
nonterminal descendant of any one source.

## Universal coefficientwise and exact physical certificates

`oracles/python/class_a_nine_swap_to_x.py` verifies the paths
**over all of Z[k,t]**, not by fitting finite specimens.
The incidence action is

    M(p,q,r)=(2p+q+r,q+r,A p+n q+(n-1)r).

For each of the **34 base selected occurrence transitions**
(and 34 actual reversed ones), it recomputes literal proper
prefix vectors of FIRST/RUN/LAST occurrences, checks integer-cone
RUN index bounds, and proves all target Parikh coefficients by

    w' = Mw + P_bottom(j) - P_top(i).

This gives **68 exact symbolic oriented edges**, all ending
at the correct X orientation. Adding X->Q->C is checked
independently as exact coefficientwise transport.

For the inherited Perron root, use the already established
finite rational inequalities 0<h<1/5, h<rho, rho+2h<1, with
Ly=1, Lx=2+rho, Lc=1+h.
All physical margins are integer-affine in 1,h,rho. Checking
the rational closure vertices (0,0),(0,1),(1/5,1/5),(1/5,3/5)
shows the margins are nonnegative at each vertex and nonzero,
hence strictly positive throughout the open chamber.
The executable check covers **32 distinct oriented path
states and 64 strict margins**. It does not reprove the
inherited Perron localization and uses no tile-length
independence premise.

Separately, the literal-word/Fraction oracle checks
0<=k<=12, 0<=t<=8: **117 specimens and 7,956 actual
occurrence-edge replays**, both true orientations, with
all full Parikh offsets and strict physical guards.
Finite replay is a regression, not the basis of universal
quantification.

## A concrete one-way-coverage counter-calibration

**Seed reaches X is not the same as X reaches seed.**

At the exactly checked member (k,t)=(3,0), the complete
coincidence-terminalized closure of the four distinguished
seeds X,Y0,CY,CC contains **350 vertices** but
**does not contain S1=(x,x,0,1,0)**, even though this
valid swapped-patch seed has a uniform *three-edge path
to X*. The nine swapped-patch seed closure at this
same member contains **351 vertices**, including S1.
This is a finite, fully explicit counterexample to
identifying the two seed-generated closures.

The finite four-seed X-hub observation in PR #427
therefore **cannot** be promoted into all-nine-seed
*forward closure* by using these nine *backward-to-X*
paths. A separate inclusion or component argument
would be needed. The current result establishes the
nine seeds' own selected productivity, not the
productivity of all states reachable *from* them.

## Next actual global proof obligations

1. Prove a **parameterized accessibility certificate**
   sending every nonterminal descendant of all nine
   swapped-patch seeds to a productive hub such as X,
   without relying on incomplete or capped finite graphs.
2. Establish the separate bridge between this
   swapped-patch closure and all relevant realized
   overlap/strict-zipper classes; do not assume that
   a graph formed from nine swaps is the literature
   overlap graph.
3. Keep finite SCC census, actual star classification,
   selected-exit sources, hosted checks and independent
   human review as different evidence categories.

General BH/#139, G1, A1-prime, PDS and PSC remain open.
