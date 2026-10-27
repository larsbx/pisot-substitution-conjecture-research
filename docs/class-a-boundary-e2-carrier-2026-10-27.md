# E2 and Dxx: complete stars and five-step typed exits

## Hypotheses and exact field identities

Continue [the P carrier](class-a-boundary-p-carrier-2026-10-27.md) on the
minus boundary: integers k,t>=0, n=k+t+3, d=2n-1-k,
A=n+d=2n+t+2, N=n-1. Ordered images are x y^A x, c y^n x,
x y^N c. The full bottom-minus-top offset is z=(x,c,y), transported by

    Mz=(2x+c+y, c+y, (n+d)x+n*c+(n-1)y).

Normalize Ly=1 and put h=1/beta, alpha=beta-(n+2),
a=Lx=2+alpha-h, b=Lc=1+h, v=alpha+h.
The inherited polynomial certificates prove

    0<h<1/5, h<alpha<1, 0<v<1, 0<alpha+2h<1, 2<a<3.

In particular E2=(x,x,0,0,2) is a genuine strict physical overlap.
It is A2h's actual FIRST/FIRST child (0,0) throughout the chamber.
The other new packet is Dxx=(x,x,1,2,-4), whose shift is v in (0,1).
Dxx has the same offset coordinates as D from the preceding increment,
but its bottom tile is x. Both child words now have A run occurrences;
D's bottom word had N. Tile types cannot be erased from the carrier.

Their incidence images and inflated physical shifts G are

| Source | Mz | G=beta*s |
| --- | --- | --- |
| E2 | (2,2,2n-2) | 2beta |
| Dxx | (0,-2,t+6) | t+4-2h |

Include both actual reversals R(top,bottom,z)=(bottom,top,-z).
These are four oriented packets, with actual child indices swapped under R.
The [stop/go](class-a-boundary-e2-stopgo-2026-10-27.md) reuses the same
three-primary-source review and physical/every-overlap/internal-space firewalls.

The exact H3 separator is inherited, not recomputed by a numerical estimate:

    8f(n+5/2)=4k^2+20k-4t^2-24t+5,
    e=1 iff alpha>1/2 iff t>k or (t=k>=2).

Equality is impossible; e=0 includes (0,0) and (1,1). Its coefficientwise
cone proof and positive root brackets are replayed by the dependency certificate.
The cubic is f(X)=X^3-(n+2)X^2-(t+3)X+2, and
beta*alpha=t+3-2h. In particular alpha>h is exact.

## Complete nine-kind child tables

Both parent tile types are x. FIRST is index 0 with child x and zero prefix;
RUN i, 1<=i<=A, has child y and prefix (1,0,i-1);
LAST A+1 has child x and prefix (1,0,A).
Their physical prefixes are 0, a+i-1 and a+A.
A child shift is G+prefix_bottom(j)-prefix_top(i).
Require -length(bottom child)<shift<length(top child), strictly.

All run bounds in this table are clipped to 1..A. A diagonal strip is empty
if no actual run indices survive. A dash means no geometrically interior child.

| Kind | E2 | Dxx |
| --- | --- | --- |
| FIRST/FIRST | - | - |
| FIRST/RUN | - | - |
| FIRST/LAST | - | - |
| RUN/FIRST | i=2n+3..min(A,2n+5+e); j=0 | i=t+2,t+3,t+4; j=0 |
| RUN/RUN | i-j=2n+4+e,2n+5+e | i-j=t+3,t+4 |
| RUN/LAST | - | - |
| LAST/FIRST | (A+1,0) iff t<=2 or (t=3,e=1) | - |
| LAST/RUN | i=A+1; j=max(1,t-2-e)..t | i=A+1; j=2n-1,2n,2n+1 |
| LAST/LAST | - | - |

For E2 the RUN/FIRST shift is 2n+3+v-i. The upper guard gives
 i>=2n+3 and the lower guard i<2n+5+2alpha, yielding exactly the
e-dependent upper endpoint. RUN/RUN is 2n+4+2alpha+j-i;
strictness gives the two displayed diagonals. LAST/FIRST has shift v-t,
and its only nonautomatic margin is a+v-t=2+2alpha-t>0. This is
exactly t<=2 or t=3,e=1. LAST/RUN is j-t+1+2alpha; its two
margins give j>=t-2-e and j<t+1-v, hence j<=t.

For Dxx, RUN/FIRST is t+3-v-i. Its two margins are equivalent to
t+2<=i<=t+4, since a-v=2-2h. RUN/RUN is t+4-2h+j-i,
giving the two displayed diagonals. LAST/RUN is j-2n+1-2h;
the lower guard gives j>=2n-1 and upper guard j<2n+1+v, hence
j<=2n+1. These three indices exist since A-(2n+1)=t+1>0.

All empty kinds are excluded as follows. In both sources G>a:
for E2 this is immediate from beta-a=n+h, and for Dxx,
G-a=t+2-v>0. FIRST/FIRST and LAST/LAST therefore lie past their
upper margin; FIRST/RUN and FIRST/LAST increase it further.
RUN/LAST has shift G+A-i+1>=G+1>1, beyond its top y.
For Dxx, LAST/FIRST has lower margin G-A=2-2n-2h<0.
These are universal inequalities, not absences observed on a finite grid.

Set q=3+e. E2 has min(t,q) RUN/FIRST children, min(t,q) LAST/RUN,
max(0,t-q+1)+max(0,t-q) RUN/RUN and one LAST/FIRST iff t<q.
Splitting t<q and t>=q gives exactly 2t+1 children.
Dxx has 3 RUN/FIRST, (A-t-3)+(A-t-4) RUN/RUN and 3 LAST/RUN,
exactly 4n+3 children. Its diagonal lengths are positive since
A-t-4=2n-2>=4. The reversed stars have the same counts.
Production synthesis follows these strips in O(n+d) time and output space.

## Symbolic transport and exact 46-label outgoing union

The canonical coefficientwise certificate checks Mz, all nine kind identities
on the affine ordinal basis 1,2, both orientations, and all selected cone-legal
indices. It reuses the existing indexed-prefix kernel rather than assuming
that a syntactic last letter is a run occurrence.
The Perron-field identities are checked after clearing the positive beta
factor and reducing modulo f:

    beta*a=beta^2-n*beta-1, beta*b=beta+1,
    beta*G_E2=2beta^2, beta*G_Dxx=(t+4)beta-2.

A corrupted field identity refuses. The preceding inequalities supply the
geometric guards; full literal-word transport independently rechecks every
submitted member edge and intended target.

The base-oriented outgoing list has 23 labels. Its reversal is disjoint,
so the entire chamber-wide union has exactly 46 labels:

| Source/kind | Complete target labels, with y the last coordinate |
| --- | --- |
| E2 RUN/FIRST | (y,x,1,2,y), y=-7..-4 |
| E2 RUN/RUN | (y,y,2,2,y), y=-8..-6 |
| E2 LAST/FIRST | (x,x,1,2,y), y=-7..-4 |
| E2 LAST/RUN | (x,y,2,2,y), y=-8..-5 |
| Dxx RUN/FIRST | (y,x,-1,-2,y), y=3..5 |
| Dxx RUN/RUN | (y,y,0,-2,y), y=2,3 |
| Dxx LAST/RUN | (x,y,0,-2,y), y=2,3,4 |

Each stated label has an actual exact occurrence witness in the archived
receipt. Symbolic cancellation and the guard table give universal containment;
the finite witnesses give existential attainment, without extrapolation.
This is a union over parameters, not 46 labels in every member.

## Five-step typed paths and the forced endpoint

The previously classified suffixes are J->K->L->H1->C at
(t+2,0),(k+1,0),(0,n-2),(1,2), where C=(y,y,0,0,0).

* At t>=1, E2 reaches J=(y,x,1,2,-4) at (2n+3,0).
  The run bound is A-(2n+3)=t-1>=0. This gives a five-step path to C.
* At t=0, 2n+3=A+1 is LAST x, not RUN y. The complete table gives
  exactly one child, Dxx at (A+1,0). Its full offset is (1,2,-4).
  Dxx reaches K=(y,x,-1,-2,5) at (t+2,0), giving another five-step path.
* Dxx itself has a four-step path: Dxx->K->L->H1->C, uniformly in k,t.

The t>=1 polynomial occurrence check substitutes t=t'+1, n=n'+1,
d=d'+2 into the full cone. The t=0 check uses n=k+3,d=k+5 and the
LAST prefix. Both actual reversed paths swap each ordinal and reverse each
full target. The native test explicitly refuses a universal unshifted RUN at
2n+3, since the full cone includes t=0 and A-(2n+3)=-1 there.
The ordinal exists at that endpoint; the asserted run type does not.

The selected thirteen-label packet has rank E2=5, Dxx=4, J=4, K=3,
L=2, H1=1, C=0, with identical ranks under reversal.
All selected edges strictly decrease. Rank is undefined elsewhere, and a
correct terminal cannot excuse a corrupted intermediate target or occurrence.
No all-edge descent measure is asserted.

For k>=2 there is also an actual six-cycle: at t=0 use
E2->Dxx->K->L->P->A2h->E2, while at t>=1 replace Dxx by J.
L->P uses (1,n), P->A2h uses (1,t+4), and A2h->E2 uses (0,0).
The run bound N-(t+4)=k-2 proves that part's precise range.
L has its H1 exit. This is not a closed obstruction.

## Replay, controls and remaining case

Canonical implementation, driver and test are
`kernel/psc/class_a_boundary_e2_children.mojo`,
`kernel/class_a_boundary_e2_children.mojo`, and
`kernel/tests/test_class_a_boundary_e2_children.mojo`.

```sh
cd kernel
pixi run --locked mojo run -I . class_a_boundary_e2_children.mojo
pixi run --locked mojo run -I . tests/test_class_a_boundary_e2_children.mojo
```

Local locked Mojo 1.1.0.dev2026090805 covers 56 members (k=0..7,t=0..6),
164,192 ordered pairs, 5,376 accepted and 1,008 selected path edges.
All 46 labels are attained. Every actual word pair is compared with the exact
native Parikh/Perron child, including both orientations and duplicates refused.

Independent literal-prefix/integer-polynomial/Fraction replay covers 117 members
(k=0..12,t=0..8), 468 source cells, 595,296 ordered pairs,
14,976 accepted and 2,106 selected path edges. It independently checks the
algebraic half separator and strict child geometry with a fixed 512-refinement
budget; unresolved signs raise rather than choose a verdict.

```sh
python -m pytest -q tests/test_class_a_boundary_e2_children.py
python oracles/python/class_a_boundary_e2_children.py > /tmp/boundary-e2.json
cmp /tmp/boundary-e2.json evidence/class-a-boundary-e2-2026-10-27/probe.json
```

A deliberate invalid geometric control uses Dxx(t+3,1): its target
(y,y,0,-2,4) has shift 2-2h>1, so its intervals are disjoint.
Dxx(A+1,2n+1) has the same offset but target (x,y,0,-2,4),
which is strictly interior since 0<2-2h<2<a. Both pairs are word-legal.
Other controls cover the t=3 half-chamber endpoint, invalid ordinals, corrupt
symbolic fields, wrong tile types and terminals, duplicate synthesis,
out-of-packet rank and broken intermediates with a correct final C.

Exact receipts, input digests and SHA256SUMS are in
`evidence/class-a-boundary-e2-2026-10-27/`; the dedicated hosted workflow is
`.github/workflows/class-a-boundary-e2.yml`. Fresh applicable native, Python,
Lean, TLA, source-provenance and evidence-policy checks at the actual head
remain integration gates. Local Lean's launcher failure before compilation
is not a proof pass. No new Lean/TLA source or governed status is added here.
Main's existing 124 claims and 34 named proofs are preserved; human review pending.

The next unclassified source is H4=(x,y,0,-2,4), reached from Dxx at
(A+1,2n+1) for every member. Its run/run lookalike is deliberately excluded
as disjoint; H4 itself is a real child. The 46-label union is not proved
forward closed. Coverage of all relevant cyclic strict zippers, plus chambers,
target-aware BH and non-unit internal-space realization remain separate gaps.
Universal BH/#139, A1-prime, G1 and PSC retain their open statuses.
