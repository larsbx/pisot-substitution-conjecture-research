# A uniform four-edge X ↔ reversal bridge (minus class A)

**Status:** exact local all-parameter symbolic proof plus independent
literal-word/Fraction regression. This is a structural SCC and
orientation theorem for a particular source, **not** a productive
carrier, all-descendant boundary-hitting theorem, G1 or PSC.
Hosted exact-head CI and independent human review are pending.

## Hypotheses, canonical states, and explicit bridge

Throughout the minus class-A chamber, let integers k,t>=0,
n=k+t+3, d=k+2t+5, A=n+d, and use exactly

    x -> x y^A x, c -> c y^n x, y -> x y^(n-1) c.

Every state is the full oriented five-tuple
(top,bottom,dx,dc,dy) with bottom-minus-top integer
Parikh displacement. An edge is the actual ordered pair of
zero-based child indices passing strict physical overlap.

Let

    X   = (x,x, 1, 0,-1)
    B3  = (y,x, 0,-1, 0)
    H1  = (x,y, 0,-1, 1)
    Z   = (y,c, 0, 0,-1)
    R(X)= (x,x,-1, 0, 1).

The following four **actual indexed** transitions are
valid for every k,t>=0:

    X   --(d+2,0)--> B3
    B3  --(0,n+2)--> H1
    H1  --(n,n)----> Z
    Z   --(0,n+1)--> R(X).

At the H1(n,n) edge, the top x image selects a
RUN y, whereas bottom y image selects the **LAST c**.
At the Z(0,n+1) edge, top y selects FIRST x and bottom
c selects **LAST x**. Neither LAST occurrence can be
silently relabeled RUN.

Actual reversal of every directed edge transposes its
two indices, reverses top/bottom types and negates
the entire Parikh displacement. Applying reversal to
the path above gives a second four-edge path
R(X) -> R(B3) -> R(H1) -> R(Z) -> X.

Consequently X and R(X) lie in the same actual
strongly connected component for every k,t>=0.

## Exact arithmetic and strict geometry

The proof checker
`oracles/python/class_a_x_reversal_hub.py` treats
n=k+t+3 and d=k+2t+5 as affine integer triples,
checks every literal FIRST/RUN/LAST word-index bound
on the **entire unbounded parameter cone**, and
recomputes all three integer Parikh coordinates by

    w' = M w + P_bottom(j) - P_top(i),
    M(p,q,r)=(2p+q+r,q+r,A p+n q+(n-1)r).

It verifies all four displayed edges and all four actual
reversals as **eight** coefficientwise symbolic directed
transports, not extrapolations from finite specimens.

Let h=1/beta and rho=alpha-h. The already established
class-A exact root inequalities give

    0<h<1/5,  h<rho,  rho+2h<1,

and Ly=1, Lx=2+rho, Lc=1+h. The physical shift
of (top,bottom,p,q,r) is
`(2p+q+r) + q*h + p*rho`.
The two required strict overlap margins
s+Lbottom and Ltop-s are affine in (1,h,rho).
For each of the **eight distinct oriented path labels**,
both margins are certified by checking the four exact
rational closure vertices (0,0),(0,1),
(1/5,1/5),(1/5,3/5) and requiring a nonzero affine
functional. Thus **16 exact strict margins** hold
throughout the open Perron chamber, conditional
on the inherited root localization.

The independent literal-word/Fraction regression checks
117 parameter specimens (k=0..12,t=0..8), both actual
orientations: **936 selected directed indexed bridge
edges**. In addition, for each of the five base
intermediate states, it explicitly checks the
**entire literal ordered occurrence domain** against
the corresponding reversed child identity and strict
overlap equivalence. No floating-point sign is used.
Six locally executed regression tests passed, including
three complete finite X-closure reversal tests and
negative controls for false types, bad cone indices
and disjoint targets. The committed exact source
Git blob matches the locally executed version
(SHA 4f82e53f612333bf6fd3ae2f582dcb38a5813016).
Fresh hosted tests against the repository's original
Geometry and standard integrity gates remain required.

## General reversal lemma and universal source-closure consequence

For every actual child transition w -(i,j)-> v,
the full Parikh rule and linearity of M imply

    R(v) = child(R(w),j,i).

The target's strict physical margins interchange
under s -> -s and swapping source tile types.
This makes R an exact directed-graph automorphism
of the full strict occurrence-indexed overlap graph.
It also preserves typed equal-letter zero-offset
coincidence terminals, so the result holds after
coincidence terminalization used by SCC diagnostics.

Given any path X ->* v, apply R to each of its
edges to obtain R(X) ->* R(v), then prepend the
four-edge X -> R(X) bridge. Hence

    R(Reach(X)) = Reach(X)

for the **complete forward X-generated strict graph**
at every minus-class-A parameter, without assuming
graph finiteness or classifying all descendants.
The new executable `lifted_reversal_path` constructs
an explicit indexed witness X -> R(v) from any
valid path X -> v; tests verify real words.

In particular, if a source is known to lie in Reach(X),
its full reversal does too. This allows future
all-parameter SCC/carrier certificates to operate
on reverse-orbit representatives **provided they keep
actual indexed edges and full Parikh offsets**.

## Boundaries and next real mathematical target

This proves a two-way path between **X and its
reversal** and orientation symmetry of its
*forward-reachable vertex set*. It does not show
that **every** vertex reachable from X can return
to X, or even reach typed coincidence. The latter
is the still-open X-descendant productivity obligation
isolated by the conditional nine-seed closure work
in #428 -> #430 -> #431. Likewise, membership in
an X-reversible closure is not the missing
seed-to-literature realized-overlap coverage bridge.

No source proof-bank claim is promoted, no historical
receipt is altered, and no PSC/BH, A1-prime or
non-unit realization conclusion follows.
