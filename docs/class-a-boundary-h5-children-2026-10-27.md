# Complete H5 stars: strict t separator and 2k+1 actual children

## Hypotheses and exact separator

Continue [H5's selected exit](class-a-boundary-h5-exit-2026-10-27.md).
Classify every first/run/last child of H5=(x,y,2,2,-5) and its actual
reversal R(top,bottom,z)=(bottom,top,-z), with actual indices swapped.
Work only on minus class A: integers k,t>=0, n=k+t+3, d=2n-1-k,
A=n+d=2n+t+2, N=n-1, and literal images x y^A x, c y^n x, x y^N c.
Retain full bottom-minus-top Parikh transport and strict interior intersection.
The [stop/go](class-a-boundary-h5-children-stopgo-2026-10-27.md) reuses
the three-primary-source review; no all-source or non-unit transfer is supplied.

Normalize Ly=1. Put h=1/beta, alpha=beta-(n+2), a=Lx=2+alpha-h,
b=Lc=1+h. Inherited exact certificates give 0<h<1/5, h<alpha<1,
0<alpha+h<1, 2<a<3. H5's shift is 1+2alpha, strictly between 0 and a
because a-(1+2alpha)=1-alpha-h>0. Its actual H4 ancestry is (A+1,t+2).

Set eta=alpha-4h and q=2d-n+3=A+2-k=n+2t+7. The cubic
f(X)=X^3-(n+2)X^2-(t+3)X+2 gives the coefficientwise identity

    beta^2*eta=(t-1)*beta-2.

At t=0,1 the right side is -beta-2,-2, strictly negative. At t>=2 it
is at least beta-2>0. Also -1<eta<1 since 0<alpha<1 and 0<4h<4/5.
Thus e=1 iff t>=2; -1<eta<0 at t=0,1, and 0<eta<1 at t>=2.
There is no equality case. The positive cone substitutes t=t'+2, with
coefficient t'+1>=1; beta>5 is inherited from the exact root bracket.
No finite sample or rounded root supplies this universal split.

## All nine child kinds

The incidence image is M(2,2,-5)=(1,-3,q+2). The inflated shift is
G=beta*(1+2alpha)=q+1+eta.
FIRST prefixes are (0,0,0), RUN i has (1,0,i-1), and LAST has (1,0,R)
for run length R. Physical prefixes are 0, a+i-1, a+R.
Top run bound is A, LAST=A+1 has child x; bottom run bound is N,
LAST=n has child c. For each actual pair impose
-length(bottom child)<G+prefix_bottom-prefix_top<length(top child).

All run ordinals in this table are clipped to their true bounds. For R(H5)
transpose the actual occurrences, negate the full target and reverse its types.

| Kind | All and only strict children of H5 |
| --- | --- |
| FIRST/FIRST | none |
| FIRST/RUN | none |
| FIRST/LAST | none |
| RUN/FIRST | i=q-1..min(A,q+1+e), j=0 |
| RUN/RUN | i-j=q+e,q+1+e; 1<=j<=min(N,A-(i-j)) |
| RUN/LAST | none |
| LAST/FIRST | (A+1,0) iff k<=2 or (k=3,t>=2) |
| LAST/RUN | i=A+1, j=max(1,k-2-e)..k |
| LAST/LAST | none |

RUN/FIRST has shift q-3h-i. Its upper guard gives i>=q-1 because
0<3h<1; its lower guard i<q+2+eta gives i<=q+1+e.
RUN/RUN has shift q+1+eta+j-i, giving exactly the two diagonals.
LAST/FIRST has shift 1-k-3h. Its upper guard is automatic and its lower
margin is a+1-k-3h=3+eta-k, yielding exactly the stated k cases.
LAST/RUN has shift j+2-k+eta: its lower guard gives j>=k-2-e and
upper guard j<k+3h gives j<=k. Since N-k=t+2>0 these indices fit the word.

All exclusions are universal inequalities. G>a since G-a=q-1-3h>0
and q>=10. FIRST/FIRST is already past its top x; FIRST/RUN and
FIRST/LAST increase it. RUN/LAST has shift at least
G+N-A+1=t+6+eta>5, beyond its top y. LAST/LAST has shift
G+N-A=t+5+eta>4>a. No excluded child is inferred absent from finite data.

Put Q=3+e. RUN/FIRST and LAST/RUN each have min(k,Q) children;
RUN/RUN contributes max(0,k-Q+1)+max(0,k-Q); LAST/FIRST contributes
one iff k<Q. Splitting k<Q and k>=Q gives **2k+1** actual children
in each orientation. At k=0 the known LAST/FIRST child is unique.
Production synthesis follows the strips and endpoints in O(n+d) time and
output space, with a fixed scalar target predicate.

## Full transport and exact image

The unchanged incidence update is

    M(x,c,y)=(2x+c+y,c+y,(n+d)x+n*c+(n-1)y),
    child=Mz+prefix_bottom-prefix_top.

The canonical certificate checks every kind on affine ordinal basis 1,2 and
actual last prefixes, in both orientations. It clears field denominators using
beta*a=beta^2-n*beta-1, beta*b=beta+1, and checks
beta*G=beta^2+(2t+6)beta-4 modulo f. Corrupt identities refuse.
The preceding inequalities supply geometric completeness. Every submitted
member edge is further checked against literal words, full Parikh transport,
strict exact Perron geometry and its intended typed target.

| Kind | Complete base target labels, y denoting the last coordinate |
| --- | --- |
| RUN/FIRST | (y,x,0,-3,y), y=1..4 |
| RUN/RUN | (y,y,1,-3,y), y=0..2 |
| LAST/FIRST | (x,x,0,-3,y), y=1..4 |
| LAST/RUN | (x,y,1,-3,y), y=0..3 |

There are 15 base labels and 15 disjoint reversals: **30 labels in the
chamber-wide outgoing union**, not 30 labels per member. Symbolic cancellation
and guards give universal containment. Archived actual k,t,i,j witnesses attain
every label; finite witnesses supply only this existential converse.

## Retained typed paths, controls and limits

Retain the original H5 path. At k=0 it goes via (x,x,0,-3,4),
(y,x,0,1,-1), C=(y,y,0,0,0) at (A+1,0),(t+1,0),(2,1).
At k=1 it uses (A+1,0) to (x,x,0,-3,3), then (1,4) to C.
At k>=2 it uses RUN q=A+2-k to (y,x,0,-3,3), then (1,4) to C.
At k=0 the q address is outside the word; at k=1 it is LAST x, not RUN y.
The new verifier replays the original path and actual H4 ancestry, constructs
and checks every reversed occurrence, and requires the intended typed terminal.
On only these selected packets, rank is 3,2,1,0 at k=0 and 2,1,0 at
k>=1, with matching reversed stages. Rank is undefined elsewhere.
The inherited native test also checks equal physical starts and strict terminal
interval interiority in both inflated parents. No all-edge rank is asserted.

At k=4, actual RUN/FIRST (q+2,0) is disjoint at t=0,1 and interior
at t>=2. At k=3, LAST/FIRST is disjoint at t=1 and interior at t=2.
Thus t=1 is neither equality nor the positive side. Controls also reject a
wrong interior target inside the image, invalid ordinals, duplicate synthesis,
corrupt symbolic fields, rank escape and altered intermediate/terminal types.
A correct final C cannot repair a broken intermediate. Previously recorded
real cycles retain their exits; no closed obstruction is inferred.

## Exact replay and remaining packet

Canonical module, driver and native regression:
`kernel/psc/class_a_boundary_h5_children.mojo`,
`kernel/class_a_boundary_h5_children.mojo`,
`kernel/tests/test_class_a_boundary_h5_children.mojo`.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_h5_exit.mojo
pixi run --locked mojo run -I . tests/test_class_a_boundary_h5_children.mojo
pixi run --locked mojo run -I . class_a_boundary_h5_children.mojo
```

Local locked Mojo 1.1.0.dev2026090805 checks 56 members (k=0..7,t=0..6),
33,096 ordered pairs, 896 accepted occurrences and 238 selected path edges,
including every reversed edge and all 30 attained labels.
Independent literal-word/integer-polynomial/Fraction replay checks 117 members
(k=0..12,t=0..8), 234 source cells, 122,616 pairs, 3,042 accepted and
486 selected edges. Its fixed 512-refinement sign budget raises if inconclusive.

```sh
python -m pytest -q tests/test_class_a_boundary_h5_children.py
python oracles/python/class_a_boundary_h5_children.py > /tmp/h5-children.json
cmp /tmp/h5-children.json evidence/class-a-boundary-h5-children-2026-10-27/probe.json
```

Receipts, input digests and SHA256SUMS are in
`evidence/class-a-boundary-h5-children-2026-10-27/`. Dedicated hosted workflow
`.github/workflows/class-a-boundary-h5-children.yml` replays the inherited exit
and complete table. Exact-head native, full Python, Lean, TLA, provenance and
evidence-policy gates remain required before integration. Local Lean's launcher
failure before compilation is not a proof pass. No new Lean/TLA source,
proof inventory or governed status is added: retain main's 124 claims and
34 named proofs, with independent human review pending.

One explicit next unclassified source is F=(x,y,1,-3,3), reached by
H5's actual LAST/RUN (A+1,k) when k>=1. Its shift is 2+eta, interior
because a-(2+eta)=3h>0. At k=0, j=0 is not a RUN, so this ancestry
is not extended there. F's full star and other target descendants remain
unclassified here. The 30-label outgoing union is not proved forward closed.
All-source strict-zipper coverage, plus chambers, target-aware BH and non-unit
internal-space realization remain separate obligations. Universal BH/#139,
A1-prime, G1 and PSC stay open.
