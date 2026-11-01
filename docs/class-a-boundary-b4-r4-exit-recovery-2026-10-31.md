# Selective recovery of B4 and R4 uniform coincidence exits

**Integration candidate (2026-11-01):** canonical native counterparts and
fresh cross-checks are recorded in
[the research integration audit](research-branch-integration-2026-11-01.md).
The original 2026-10-31 scopes and main/research distinctions below are
historical; they do not imply acceptance of this candidate. Exact-head
hosted acceptance remains required. Independent human review is pending.
Pending human review is validation debt, not an additional premise for
project acceptance once mathematical, replay, CI and governance checks pass.

**Status:** mathematically scoped exact selected-exit certificates, recovered
from research PRs #377 (B4 and companions) and #378 (R4 and companions).
Original source-star proofs, archived receipts, and branch histories are
preserved; **no** complete-star classification or general PSC claim is
imported by this PR. The new independent hand-to-executable extraction
has passed local standalone exact arithmetic checks. Independent human
review and fresh exact-head hosted acceptance remain outstanding.

## Entire minus class-A chamber

For all integer k,t>=0 use n=k+t+3, d=k+2t+5, A=n+d and actual
x->x y^A x, c->c y^n x, y->x y^(n-1) c.
Overlap labels are actual oriented (top,bottom,dx,dc,dy) with full
bottom-minus-top Parikh offsets. Genuine reversal swaps actual ordered
occurrence indices and negates all three Parikh coordinates.

B4=(y,x,0,-1,-1), R4=(x,y,1,-1,-2).
C=(y,y,0,0,0), Q=(y,x,0,-1,1),
RH=(y,x,0,1,-1), H=(x,y,0,1,-1),
RL=(x,y,0,-3,4), RK=(x,y,1,2,-5).
All paths use **actual** zero-based word ordinals, not label quotient edges.

## B4 selected exits (three exact t chambers)

| Parameter | Fully typed selected occurrence path | Depth |
| --- | --- | ---: |
| t=0 | B4 -(0,A+1)-> D0=(x,x,-1,-2,3) -(0,d+3)-> H -(2,1)-> C | 3 |
| t=1 | B4 -(0,A+1)-> DXR=(x,x,-1,-2,4) -(0,t+2)-> RK -(0,k+1)-> RL -(n-2,0)-> RH -(2,1)-> C | 5 |
| t>=2 | B4 -(0,2n+4)-> F4=(x,y,-1,-2,4) -(0,t+2)-> RK -(0,k+1)-> RL -(n-2,0)-> RH -(2,1)-> C | 5 |

The `t=1` B4 child at bottom ordinal `2n+4=A+1` is
an actual **LAST x** with label DXR, not the fictitious RUN y F4.
At `t>=2` the same affine ordinal is a real RUN, producing F4.
At `t=0` the valid selected LAST index is `A+1`, not the
nonexistent RUN `2n+4=A+2`. All endpoint branches remain distinct.

## R4 selected exits (three exact t chambers)

| Parameter | Fully typed selected occurrence path | Depth |
| --- | --- | ---: |
| t=0 | R4 -(0,n)-> E4=(x,c,0,-3,3) -(0,3)-> H -(2,1)-> C | 3 |
| t=1 | R4 -(0,k+3)-> D4=(x,y,0,-3,3) -(0,3)-> Y4=(x,y,1,0,-1) -(d+1,0)-> Q -(1,2)-> C | 4 |
| t>=2 | R4 -(0,k+4)-> RL -(n-2,0)-> RH -(2,1)-> C | 3 |

At `t=0`, R4's first bottom index `n` is actually the
LAST `c` of the y image. When `t>=1`, the selected bottom indices
are genuine RUN y positions. Every conditional path remains
valid for k=0 as well as for unbounded k.

## Exact unbounded verification, independently implemented

The separate file `oracles/python/class_a_boundary_b4_r4_exit_recovery.py`
uses a finite affine-polynomial checker over Z[k,t]. Each of the six
(source,t-chamber) paths is checked against the actual
FIRST/RUN/LAST proper prefix of each literal word, with
recession-safe index inequalities throughout each unbounded integer
chamber. Every edge checks complete typed target equality using
`w'=Mw+P_bottom-P_top` and the full three-coordinate
incidence action `M(p,q,r)=(2p+q+r,q+r,A*p+n*q+(n-1)*r)`.
It verifies **46 directed symbolic transitions including actual
reversal**, rather than extrapolating from finite specimens.

For strict physical overlap, put `h=1/beta`,
`rho=alpha-h`, `Ly=1`, `Lx=2+rho`,
`Lc=1+h` and reuse the exact inherited bounds
`0<h<1/5`, `h<rho`, `rho+2h<1`.
The four exact rational vertices of this open polygon's
closure certify **50 strict physical margins across 25 distinct
oriented path states**, conditional on the inherited root bounds.
No tile-length independence, numerical root estimate or analytic
transfer is introduced.

## Independent finite validation, status, nonclaims

The local checked Python source blob (Git SHA
`260733a49b0ec54f43f7d4299fd31feea3841007`) passed its symbolic
certificate and an independent **117-parameter / 1,846 selected-edge**
literal-prefix/Fraction Perron replay on k=0..12, t=0..8 with both
true orientations. The hosted exact-head workflow must repeat that
validation using the actual repository Geometry and its provenance gates.
Negative controls include wrong LAST/RUN typing, corrupted target
coordinates, disjoint geometry and invalid unbounded word index slopes.

This proves uniform *selected* coincidence exits for B4 (<=5) and
R4 (<=4), **not** their complete outgoing stars, every-direct-child
productivity, forward closure, SCC coverage or any general BH/PSC
claim. Together with focused PR #424 (R3/B3/R5) and #420 (T2),
these would supply the six still-research-only X first-child
selected-exit interfaces audited by #421, once each is independently
accepted. Keep the conditional/unconditional status firewall until then.
