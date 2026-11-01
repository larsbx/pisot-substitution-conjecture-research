# T's forced child, the X return cycle and complete Y0 children

**Consolidation notice (2026-10-31):** this source retains #371's historical symbol
`T=(x,y,1,-1,1)`, which is named `Q3` in the current mainline #373
stack. The oriented five-tuple, not its nickname, is canonical. The
source's historical P3 link now targets main's accepted #372 carrier.
See [canonical reconciliation](class-a-boundary-tx-consolidation-2026-10-31.md).


## Hypotheses and scope

Continue [P3](class-a-boundary-p3-carrier-2026-10-28.md) under the
[same scoped stop/go](class-a-boundary-tx-stopgo-2026-10-28.md).
Use minus class A: k,t>=0, n=k+t+3, d=2n-1-k, A=n+d, N=n-1,
and exactly x->x y^A x, c->c y^n x, y->x y^N c.
Offsets retain full bottom-minus-top integer Parikh vectors. Reversal swaps
both tile types and actual indices and negates all three coordinates.

Normalize Ly=1. Put h=1/beta, alpha=beta-(n+2), rho=alpha-h,
theta=alpha-2h, v=alpha+h, a=Lx=2+rho and b=Lc=1+h.
The inherited exact polynomial certificates establish
0<h<1/5, 0<rho,theta,v<1, and 2<a<3.
In particular beta^2*theta=(t+1)*beta-2>0; no numerical sign is used.

Classify three sources and their real reversals (six oriented stars):

| Source | Full label | Physical shift | Incidence image | Inflated shift G |
| --- | --- | --- | --- | --- |
| T | (x,y,1,-1,1) | a-h=2+theta | (2,0,A-1) | A+3+2rho |
| X | (x,x,1,0,-1) | a-1 | (1,-1,d+1) | d+2+theta |
| Y0 | (y,y,1,-1,-1) | theta | (0,-2,t+3) | t+1-2h |

All are strict physical overlaps: T's upper margin is h; X's is 1;
Y0 has shift in (0,1). T is P3's actual LR(A+1,n-2) child throughout
the chamber. X is the already classified X of
[the W/X carrier](class-a-boundary-w-carrier-2026-10-27.md), whose canonical
star synthesis and guard are reused rather than reimplemented.
Y0 is X's actual RR(d+3,1) child; A-(d+3)=n-3>=0.
All ancestry identities are checked coefficientwise, including reversal.

## Complete nine-kind tables

For a parent x or y with run length R, physical prefixes are
FIRST 0, RUN i: a+i-1, LAST R+1: a+R.
LAST is x for sigma(x), c for sigma(y). Require
-length(bottom child)<G+prefix_bottom-prefix_top<length(top child).
All indices below have their actual run bounds; an empty range supplies no edge.

| Kind | T (top A, bottom N) | X (both A) | Y0 (both N) |
| --- | --- | --- | --- |
| FIRST/FIRST | none | none | (0,0) iff t<=1 |
| FIRST/RUN | none | none | none |
| FIRST/LAST | none | none | none |
| RUN/FIRST | none | i=d..d+3, j=0 | i=max(1,t-1)..t+1, j=0 |
| RUN/RUN | none | i-j=d+2,d+3 | i-j=t,t+1 |
| RUN/LAST | none | none | none |
| LAST/FIRST | (A+1,0) | none | none |
| LAST/RUN | none | (A+1,j), j=n-2..n+1 | (n,j), j=k+2..min(N,k+3) |
| LAST/LAST | none | none | (n,n) iff t=0 |

For a RUN/RUN diagonal delta=i-j impose 1<=j<=R-delta, with R=A
for X and R=N for Y0. Reversal transposes the table and reverses every target.
The following inequalities prove the table over the unbounded chamber.

* **T.** RF has shift A+2+rho-i>=a>1. RR is at least
  4+2rho>1, and RL at least N+4+2rho>1. LF has shift a-1 and
  is strictly interior in x/x. LR is 2+2rho+j>=3+2rho>a;
  LL is N+3+2rho>a. FF exceeds a, and FR/FL increase it.
  Thus **T has exactly one genuine child, X**.
* **X.** RF has shift d+1-h-i, lower margin d+3+theta-i
  and upper margin i-d+h. Thus i=d..d+3, all true runs even at n=3.
  RR has shift d+2+theta+j-i, giving the two diagonals.
  LR has shift j-n+1+theta, lower margin j-n+2+theta and upper
  margin n+1+h-j, giving n-2<=j<=n+1. FF and LL exceed a
  by d-h>0; FR/FL increase it. RL is at least d+3+theta>1.
  LF has shift -n-h, with lower margin 2+theta-n<0, so is disjoint.
* **Y0.** FF has positive shift t+1-2h, with upper margin
  a-G=1+v-t. Hence it exists exactly at t=0,1. FR and FL exceed a.
  RF is t-v-i: its margins give t-1<=i<=t+1, clipped at i=1.
  RR has shift t+1-2h+j-i, giving i-j=t,t+1.
  RL is at least t+2-2h>1. LF is -k-3-v, whose lower margin
  against -a is -k-1-2h<0. LR is j-k-2-2h: its lower margin
  is j-k-1-2h and upper margin k+3+3h-j; since 3h<1,
  exactly k+2<=j<=k+3 survives, clipped at N. Finally LL has
  shift t+1-2h with top and bottom c. Its upper margin is 3h-t,
  positive exactly at t=0. The actual last letters must remain c/c.

The exact counts per source and per orientation are
**1, 2n+3, 2k+8-[t=0]**. X has 4+(n-2)+(n-3)+4 children.
Y0's RR counts are k+2 and k+1. At t=0 its FF/RF/LR/LL counts
are 1/1/1/1, giving 2k+7. At t=1 they are 1/2/2/0,
and at t>=2 they are 0/3/2/0, giving 2k+8 in both cases.
Production synthesis follows O(n+d) strips/endpoints and reuses X's accepted
implementation; exhaustive Cartesian word enumeration is confined to tests.

## Full targets and a 42-label outgoing union

Use M(x,c,y)=(2x+c+y,c+y,A*x+n*c+N*y) and then actual bottom prefix
minus top prefix. The canonical Q[t,k] identities check all nine kinds on
legal affine index bases 1,2 and actual last prefixes, in both orientations.
The positive-denominator identities beta*a=beta^2-n*beta-1 and
beta*b=beta+1 give these exact reductions modulo the characteristic cubic:

| Source | beta*G |
| --- | --- |
| T | 2beta^2+(t+1)beta-2 |
| X | beta^2+(t+2)beta-2 |
| Y0 | (t+1)beta-2 |

The complete base targets are:

| Source/kind | Full labels; y denotes the final coordinate |
| --- | --- |
| T LF | X |
| X RF | (y,x,0,-1,y), y=-1..2 |
| X RR | (y,y,1,-1,y), y=-2,-1 |
| X LR | (x,y,1,-1,y), y=-2..1 |
| Y0 FF | (x,x,0,-2,3) at t=0; (x,x,0,-2,4) at t=1 |
| Y0 RF | (y,x,-1,-2,y), y=3..5 |
| Y0 RR | (y,y,0,-2,y), y=2,3 |
| Y0 LR | (c,y,0,-2,y), y=2,3 |
| Y0 LL | (c,c,0,-2,3), only at t=0 |

There are 21 distinct base labels and 21 disjoint reversals: **42 labels**
in the parameter-chamber union. Exact cancellation gives containment;
archived actual witnesses attain every label. This finite existential direction
is separate from the universally quantified guard proof. An outgoing image
is not automatically a forward-closed carrier or an all-target productivity result.

## Selected exits and a genuine two-cycle

Let Q=(y,x,0,-1,1), B=R(B2h)=(y,y,0,-2,3),
RH1=(y,x,0,1,-1), and C=(y,y,0,0,0).

| Source | Actual selected typed path | Length |
| --- | --- | --- |
| T | (A+1,0)->X, (d+1,0)->Q, (1,2)->C | 3 |
| X | (d+1,0)->Q, (1,2)->C | 2 |
| Y0 | (t+1,1)->B, (N,0)->RH1, (2,1)->C | 3 |

The Y0 suffix reuses the canonical reversed B2h path. Every step is checked
against actual words, full Parikh transport, strict Perron geometry and its
intended intermediate packet. Reversal swaps every actual occurrence pair.
The selected rank is T/Y0:3, X/B:2, Q/RH1:1, C:0 (also reversed),
and refuses labels outside that packet. All selected edges decrease it.

Nevertheless the actual return X LR(A+1,n+1)->T is available for every
member, since n+1<=A. Together with T's forced LF edge this gives a real
uniform two-cycle T->X->T. X has the certified Q->C exit. Consequently
this cycle is not a closed obstruction; a strict rank decreasing along
**every** actual edge is impossible even on its two vertices. The return
increases the selected rank and is explicitly retained in both orientations.
X also reaches Y0 at its genuine RR(d+3,1) child, with Y0's three-step tail.
Neither of these facts proves that every other X or Y0 child is productive.

## Replay, controls and remaining symbolic case

Canonical kernel kernel/psc/class_a_boundary_tx_children.mojo, driver
kernel/class_a_boundary_tx_children.mojo and native regression
kernel/tests/test_class_a_boundary_tx_children.mojo.
From kernel/ use the locked environment and run the driver/test with
`pixi run --locked mojo run -I .`. The independent literal-prefix,
integer-polynomial/Fraction oracle is oracles/python/class_a_boundary_tx_children.py;
run tests/test_class_a_boundary_tx_children.py and compare the oracle JSON
with [the recorded replay](../evidence/class-a-boundary-tx-2026-10-28/probe.json).
Native replay: 56 members / 128,576 ordered pairs / 4,240 accepted children /
896 selected path edges. Independent replay: 117 members / 702 source cells /
470,964 pairs / 11,674 accepted / 1,872 path edges. Both attain all 42 labels.
They check implementation behavior rather than extrapolating a theorem.
Local native, scoped Python, provenance, Markdown/link/proof-bank and integrity
checks pass. All 18 TLA expected outcomes pass. Local Lean installs the pinned
toolchain but fails before compilation with `failed to locate application`;
it receives no proof credit. Preserve 124 claims, 34 named proofs and
325 source openings. Fresh exact-head hosted gates remain required.
Full receipts and source digests are archived in the evidence packet.

Controls include T's legal but disjoint RF(A,0), Y0's t=1/2 FF cutoff and
t=0/1 LL cutoff, a forged interior c/y label at an actual last/last c/c
occurrence, a wrong interior target already in the image, invalid parameters,
ordinals and orientations, symbolic field corruption, rank escape, changed
intermediates and a wrong typed terminal despite zero final offset.

The next specific uniform kernel obligation is (c,y,0,-2,2), Y0's actual
LR(n,k+2) child: N-(k+2)=t>=0. Its shift is -2h, strictly inside (-1,b).
The canonical certificate checks its full symbolic transport and actual bounds.
Its complete child star and productivity are not supplied in this increment.
The t=0 c/c packet and other descendants also remain separate obligations.

The 42-label image is not proved forward closed. This does not supply
all-source cyclic strict-zipper coverage, plus chambers, target-aware BH
or non-unit internal-space/return-lattice realization. Universal BH/#139,
A1-prime, G1 and PSC remain open. Independent human review remains pending.
No governed status or Lean/TLA source/proof inventory is changed.
