# Eight of nine swapped-patch seeds lie in the X SCC, uniformly in minus class A

**Status:** new scoped, parameter-universal exact occurrence-path
construction, stacked on PR #428's reverse seed-to-X paths.
The new X-to-seed transports are independently checked coefficientwise
over the integer parameters and by strict exact root inequalities.
Human review and fresh hosted acceptance remain pending.
This does **not** prove nine-seed descendant productivity, closure,
all-source BH/#139, G1, A1-prime, PDS or PSC.

## Object and decisive distinction

For every integer k,t>=0, take
n=k+t+3, d=k+2t+5, A=n+d, and the actual ordered substitutions
x->x y^A x, c->c y^n x, y->x y^(n-1) c.
All states are full oriented five-tuples
(top,bottom, bottom-minus-top Parikh x,c,y).
An edge is an actual zero-based ordered letter occurrence,
with full exact integer transport and **strict** physical overlap.

Let X=(x,x,1,0,-1). PR #428 already constructs actual paths
**from all nine literal swapped-patch strict seeds to X**
with length <=5. Here we establish the **opposite direction**
from X to **eight** of those seeds, uniformly over the chamber.
The ninth is S1=(x,x,0,1,0), also known as E6 in the
open research stack #382. A path from S1 to X does not prove
a reverse path from X to S1; indeed the complete exact
(k,t)=(3,0) graph is a concrete reverse-reachability counterexample.

## All eight paths and lengths

Here x/c/y are literal tile types; C remains an equal-letter
zero-offset coincidence only when explicitly so labeled.

| Swapped-patch seed | Full oriented tuple | Uniform depth from X |
| --- | --- | ---: |
| S0 | (x,c,0,0,0) | 4 |
| S2 | (c,x,-1,1,0) | 5 |
| S3 | (x,y,0,0,0) | 6 |
| S4 | (x,x,0,0,1) | 4 |
| S5 | (y,x,-1,0,1) | 4 |
| S6 | (c,y,0,0,0) | 2 |
| S7 | (c,c,0,0,1) | 6 |
| S8 | (y,c,0,-1,1) | 4 |

The full paths are stored as **18 distinct canonical
affine indexed transitions** and eight selected sequences
in `oracles/python/class_a_x_to_eight_swap_seeds.py`.
The 18 edges are reused across the eight certificates,
rather than relying on separate historical names.

For orientation and type calibration, two starting edges are

    X --(d+2,0)--> (y,x,0,-1,0)
    X --(d+1,0)--> Q=(y,x,0,-1,1).

A short complete example is

    X --(d+1,0)--> Q
      --(n,n+1)--> S6=(c,y,0,0,0).

The second address is an actual LAST/RUN or RUN/LAST
depending on the ordered word types; the executable
checker computes the *actual* child types, not a
field-only offset. In particular the source `Q=(y,x,0,-1,1)`
has top image y with LAST c at n, bottom image x with
RUN y at n+1, giving precisely c/y with full zero offset.
It is a noncoincident overlap, not the typed terminal C.

All other 17 distinct transitions have explicit affine indices
in k,t; several intentionally use true LAST occurrences.
No false RUN-at-LAST substitution is permitted.

## Exact universally quantified certificate

The new checker reuses PR #428's already scoped exact
`Aff(k,t,c)`, `certified_transport`, `strict`, and
reversal primitives. It invokes the full original
prefix-Parikh child rule

    w' = M w + P_bottom(j) - P_top(i),
    M(p,q,r)=(2p+q+r,q+r,A p+n q+(n-1)r),

for every selected edge in both true orientations.
It verifies all word-index inequalities with
nonnegative coefficient guards valid on the
entire cone k,t>=0, not by fitting specimen values.
Every target's **full three-coordinate** Parikh tuple
and genuine FIRST/RUN/LAST letter type is checked
as an identity in Z[k,t].

Across eight paths there are **35 base path edges** and
**70 directed symbolic occurrence checks counting reversals**,
using just 18 distinct affine transition formulas.
The 19 base intermediate states expand to
**30 distinct true oriented labels**, whose
**60 physical strict margins** satisfy the inherited
rational Perron guard certificate.

With h=1/beta and rho=alpha-h, the inherited inequalities
0<h<1/5, h<rho, rho+2h<1 imply the exact rational
four-vertex polygon in (h,rho).
Each strict margin is affine; its positivity throughout
the open chamber is checked by exact rational values
at the four closure vertices and a nonzero-functional guard.
The checker does not establish the root inequalities anew.

An independent literal-word/Fraction replay confirms
all **8,190** selected actual indexed edges across 117
parameter specimens (k=0..12,t=0..8), including true
reversals, intermediate types and strict overlap.
Finite replay supports implementation and is
**not** the basis for universal quantification.
Four locally run tests passed with the original
#428 exact arithmetic primitives mirrored in the
same repository-shaped test layout; source/test Git
blobs are byte-identical to the locally executed files.

## SCC implication and new remaining interface

Combining the two directional universal selected-path
certificates (#428: seed->X; this PR: X->seed) yields:

> For every k,t>=0, **eight of the nine** actual
> swapped-patch seed vertices lie in the same
> strongly connected component as X.

This is genuine **source-vertex SCC membership**, not a claim
that all the X SCC's descendants are complete/covered or
productive. The ninth vertex S1=E6 has a uniform path to X
but may not have a path back from X. The finite (3,0)
graph proves this asymmetry can actually occur.

For the one-exception graph criterion isolated in #429,
the first requirement is now supplied *uniformly*:
all nine seeds lie in Reach(X) ∪ {E6}.
The remaining outgoing-boundary obligation is

    every actual E6 child belongs to Reach(X) ∪ {E6}.

#382 gives a separate, research-only complete E6 star with
**2d-1 indexed children**, eight distinct labels for each
orientation and sixteen across true reversals, plus
every-first-choice selected coincidence tails.
**Every-first-choice productivity is not forward-X
membership.** Proving the eight E6 child labels
lie in Reach(X) is a concrete next target,
together with universal productive/reverse-X
accessibility for the entire X-generated closure.

A universal nine-seed/strict-zipper transfer and
complete literature realized-overlap coverage remain
separate, still-open obligations. Do not promote
the status of either research PR or any general PSC
claim from this composition alone.
