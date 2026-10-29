# F's three children: complete stars and typed exits for every first choice

## Hypotheses and scope

Continue [the H5 complete star](class-a-boundary-h5-children-2026-10-27.md).
Use minus class A only: integers k,t>=0, n=k+t+3, d=2n-1-k,
A=n+d=2n+t+2, N=n-1 and literal words x y^A x, c y^n x, x y^N c.
Offsets are full bottom-minus-top Parikh vectors, and intersection is strict.
Reversal R(top,bottom,z)=(bottom,top,-z) swaps actual occurrence indices.

Normalize Ly=1. Set h=1/beta, alpha=beta-(n+2), rho=alpha-h,
a=Lx=2+rho, b=Lc=1+h, v=alpha+h, w=alpha+2h, eta=alpha-4h.
Inherited exact polynomial certificates prove
0<h<1/5, 0<rho<1, 0<v,w<1, 2<a<3 and -1<eta<1.
The inherited separator beta^2*eta=(t-1)*beta-2 gives
 e=1 iff t>=2; eta<0 at t=0,1, eta>0 at t>=2, never zero.
The [stop/go](class-a-boundary-f-stopgo-2026-10-27.md) preserves the
three-primary-source actual/every-overlap and non-unit transfer boundaries.

Classify these four packets and each actual reversal (eight sources):

| Packet | Full label | Physical shift | Incidence image | Inflated shift G |
| --- | --- | --- | --- | --- |
| F | (x,y,1,-3,3) | 2+eta=a-3h | (2,0,A-3) | A+1+2rho |
| Z | (y,x,1,0,-2) | rho | (0,-2,t+4) | t+2-2h |
| E3 | (x,x,-1,0,3) | 1-rho | (1,3,k-2) | k+3+w |
| G2 | (x,y,2,0,-3) | 1+2rho | (1,-3,q+2) | q+1+eta, q=A-k |

E3 is local notation for the displayed label, distinct from the earlier E+.
All sources are strict physical overlaps: F has upper margin 3h>0;
Z and E3 shifts lie in (0,1); G2 has upper margin a-(1+2rho)=1-rho>0.
F's H5 LAST/RUN ancestry (A+1,k) is actual only for k>=1.
The coefficientwise prefix proof checks this on k=k'+1 with n,d shifted
by +1. At k=0, ordinal zero is FIRST x, not a RUN y; no seed ancestry
is inferred for that case. The standalone physical F theorem still covers it.

## Complete child tables

For run length R, FIRST has prefix (0,0,0), RUN i has (1,0,i-1),
LAST R+1 has (1,0,R). Their physical prefixes are 0,a+i-1,a+R.
LAST has child c for sigma(y) and x for sigma(x).
For every actual pair require
-length(bottom child)<G+prefix_bottom-prefix_top<length(top child).
All run indices in the table are clipped to their true words; an empty
clipped interval supplies no edge.

| Kind | F: top A, bottom N | Z: top N, bottom A | E3: both A | G2: top A, bottom N |
| --- | --- | --- | --- | --- |
| FIRST/FIRST | none | (0,0) iff t=0 | none | none |
| FIRST/RUN | none | none | none | none |
| FIRST/LAST | none | none | none | none |
| RUN/FIRST | (A,0) | i=max(1,t)..t+2, j=0 | i=k+2..k+4, j=0 | i=q-1..min(A,q+1+e), j=0 |
| RUN/RUN | none | i-j=t+1,t+2 | i-j=k+3,k+4 | i-j=q+e,q+1+e |
| RUN/LAST | none | none | none | none |
| LAST/FIRST | (A+1,0) | none | none | (A+1,0) iff k=0 or (k=1,t>=2) |
| LAST/RUN | (A+1,1) | i=n, j=k+1,k+2 | i=A+1, j=A-k-3..A-k-1 | i=A+1, j=max(1,k-e)..k+2 |
| LAST/LAST | none | none | none | none |

For each RUN/RUN diagonal delta=i-j, impose
1<=j<=min(bottom run count,top run count-delta).
Transpose the entire table and negate each typed target for the reversals.
Here are all guard reductions, including every excluded kind:

* **F.** RUN/FIRST has shift A+rho-i, so only i=A survives.
  LAST/FIRST is rho-1 in (-1,0). LAST/RUN is 2rho+j, whose upper
  guard j<2-rho leaves only j=1. RUN/RUN has shift at least
  2+2rho>1 since i-j<=A-1. FIRST/FIRST is beyond a, and
  FIRST/RUN and FIRST/LAST increase it. RUN/LAST is at least
  N+2+2rho>1; LAST/LAST is n+2rho>3>a.
* **Z.** FIRST/FIRST has G-a=t-v<0 exactly at t=0, and G>0.
  RUN/FIRST is t+1-v-i, giving i>=max(1,t), i<t+3-2h,
  hence i<=t+2. RUN/RUN is t+2-2h+j-i, giving the two strips.
  LAST/RUN is j-k-1-2h; its guards give k+1<=j<=k+2.
  FIRST/RUN and FIRST/LAST exceed a. RUN/LAST exceeds 1 because
  A>N and G>1. LAST/FIRST has lower margin G-N=-k-2h<0.
  LAST/LAST exceeds b since G+A-N>7.
* **E3.** RUN/FIRST is k+2+3h-i. Its guards give k+2<=i<=k+4,
  using 0<w<1. RUN/RUN is k+3+w+j-i, giving its two strips.
  LAST/RUN is k+2+w+j-A; its lower guard gives j>=A-k-3,
  upper guard j<A-k-3h gives j<=A-k-1. All are true runs since
  A-k-3>=5. FIRST/FIRST and LAST/LAST have G-a=k+1+3h>0;
  FIRST/RUN and FIRST/LAST increase it. RUN/LAST is at least G+1>1.
  LAST/FIRST has lower margin G-A<0, since A-k-3>=5>w.
* **G2.** RUN/FIRST is q-3h-i, giving q-1<=i<=q+1+e.
  RUN/RUN is q+1+eta+j-i, giving its two strips. LAST/FIRST is
  -k-1-3h with lower margin 1+eta-k, giving exactly its k cases.
  LAST/RUN is j-k+eta; its two guards give k-e<=j<=k+2.
  Since N>=k+2 these are true bottom runs after the lower clip.
  FIRST/FIRST exceeds a because G-a=q-1-3h>0 and q>=8;
  FIRST/RUN and FIRST/LAST increase it. RUN/LAST is at least
  t+4+eta>3, beyond its top y. LAST/LAST exceeds a by t+1-3h>0.

Consequently the exact occurrence counts per source and reversal are
3, 2k+6, 2A-2k-1, 2k+5. For Z, the missing third RUN/FIRST at t=0
is exactly compensated by FIRST/FIRST; RUN/RUN counts k+1 and k,
with two LAST/RUN children. E3 has 3+(A-k-3)+(A-k-4)+3 children.
For G2, put m=k+2 and Q=3+e: RF and LR each contribute min(m,Q),
RR contributes max(0,m-Q+1)+max(0,m-Q), and LF one iff m<Q.
Splitting m<Q and m>=Q yields 2m+1=2k+5.
Synthesis follows these strips in O(n+d) time/output space with a fixed target
predicate. It never substitutes a same-letter but disjoint candidate.

## Exact transport and 64-label image

Use M(x,c,y)=(2x+c+y,c+y,(n+d)x+n*c+(n-1)y), then add actual bottom
prefix minus top prefix. The canonical Q[t,k] certificate checks every kind
on affine index basis 1,2 and actual last prefixes, both orientations.
It also checks cleared field identities modulo the cubic:

| Source | beta*G after reduction |
| --- | --- |
| F | 2beta^2+(t-1)beta-2 |
| Z | (t+2)beta-2 |
| E3 | beta^2+(k-n+1)beta+2 |
| G2 | beta^2+(2t+4)beta-4 |

The unchanged identities beta*a=beta^2-n*beta-1 and beta*b=beta+1
clear the positive denominator. A corrupt identity refuses. The preceding
inequalities give universal guard completeness, independent of finite tests.

| Source | Complete base target labels; y denotes the last coordinate |
| --- | --- |
| F | Z, R(E3), G2 |
| Z | (x,x,0,-2,4); (y,x,-1,-2,y), y=3..5; (y,y,0,-2,y) and (c,y,0,-2,y), y=2,3 |
| E3 | (y,x,0,3,y), y=-5..-3; (y,y,1,3,y), y=-6,-5; (x,y,1,3,y), y=-6..-4 |
| G2 | (y,x,0,-3,y), y=1..4; (y,y,1,-3,y), y=0..2; (x,x,0,-3,y), y=1,2; (x,y,1,-3,y), y=0..3 |

These are 32 distinct base labels and 32 disjoint reversals: 64 labels in
the entire parameter-chamber outgoing union, not 64 in each member.
Symbolic cancellation proves containment. Archived actual k,t,i,j witnesses
prove attainment of every label. This finite existential direction is kept
separate from the universally quantified inequalities.

## Every direct F child has a typed exit; a two-cycle still survives

Let C=(y,y,0,0,0), G=(y,x,0,-3,3), B=R(B2h)=(y,y,0,-2,3),
L=(y,x,0,3,-4), H1=(x,y,0,-1,1). All indices below are actual.

| Source | Selected typed path | Length |
| --- | --- | --- |
| F | (A+1,1)->G2, then its suffix | 3 |
| Z | (t+2,1)->B, (N,0)->R(H1), (2,1)->C | 3 |
| E3 | (k+3,0)->L, (0,n-2)->H1, (1,2)->C | 3 |
| G2 | (A-k,0)->G, (1,4)->C | 2 |

The polynomial certificate checks the new first transitions and word bounds.
The B and L suffixes reuse the canonical P/H3 constructors; the G terminal
is the previously certified H5 terminal. Every supplied edge is additionally
rechecked against full literal-word transport and strict Perron geometry.
Every reversed path swaps indices and reverses the full target at every step.

F has exactly three first choices: (A,0)->Z, (A+1,0)->R(E3),
(A+1,1)->G2. Each target has a typed C tail of at most three steps,
including the reversed E3 suffix. Therefore **every genuine direct F child**
admits an existential typed tail within three steps, or a total F walk within
four. The verifier binds each chosen first edge and every intermediate target;
a correct final C does not excuse a broken path.

There is nevertheless the genuine all-chamber two-cycle

    F --(A+1,1)--> G2 --(A+1,k+2)--> F.

The second bottom index is a true run because N-(k+2)=t>=0.
Both full transports are coefficientwise certified and tested in native exact
geometry. G2's displayed G exit prevents this from being a closed obstruction.
This cycle rules out a strict all-edge descent rank on any carrier containing it.
The selected rank F=4, Z/E3=3, G2/B/L=2, G/H1=1, C=0 (and reversals)
is used only on the chosen exits; the actual G2->F edge increases it.
It is not a rank on every edge, even between these named vertices.

## Replay and remaining case

Canonical `kernel/psc/class_a_boundary_f_children.mojo`, driver
`kernel/class_a_boundary_f_children.mojo`, regression
`kernel/tests/test_class_a_boundary_f_children.mojo`:

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_f_children.mojo
pixi run --locked mojo run -I . class_a_boundary_f_children.mojo
```

Local locked Mojo 1.1.0.dev2026090805 checks 56 members (k=0..7,t=0..6),
181,384 ordered pairs, 7,616 accepted occurrences, 1,232 selected source-path
edges and 1,232 direct-F-child exit-walk edges. All 64 labels are attained;
all word pairs, full Parikh updates, strict native Perron predicates, reversal,
cycle return and all three direct choices are checked.
Independent literal-prefix/integer-polynomial/Fraction replay checks 117 members
(k=0..12,t=0..8), 936 source cells, 665,496 pairs, 20,826 accepted,
2,574 selected path edges and 2,574 direct-child exit-walk edges.
Its 512-refinement sign budget fails inconclusively rather than guessing.

```sh
python -m pytest -q tests/test_class_a_boundary_f_children.py
python oracles/python/class_a_boundary_f_children.py > /tmp/f-children.json
cmp /tmp/f-children.json evidence/class-a-boundary-f-2026-10-27/probe.json
```

Negative controls include F's word-legal disjoint (A-1,0) candidate, Z's
FIRST/FIRST disappearance at t=1, wrong interior targets already inside the
image, invalid ordinals/orientations, duplicate synthesis, rank escape,
corrupt symbolic identities and changed intermediate/terminal types.
The k=0 H5 FIRST ordinal is refused as an invented RUN ancestry.

Receipts, digests and SHA256SUMS are in `evidence/class-a-boundary-f-2026-10-27/`.
The dedicated workflow `.github/workflows/class-a-boundary-f.yml` and applicable
exact-head native/Python/Lean/TLA/provenance/evidence-policy gates remain
required before integration. Local Lean launcher failure before compilation
is not a proof pass. No Lean/TLA source, governed status or named-proof inventory
is changed; main's 124 claims and 34 named proofs remain. Human review pending.

One explicit remaining source is P3=(x,y,1,3,-4), E3's actual LAST/RUN
child (A+1,A-k-1) in every member. Its shift is 1+w<a because the upper
margin is 1-3h>0. Its reversal is reached from R(E3); F reaches R(E3)
through its real last/first child. The full P3 star is not supplied here.
The 64-label image is not proved forward closed, nor is every one of those
64 targets proved productive. All-source strict-zipper, plus-chamber,
target-aware BH and non-unit internal-space gaps remain. Universal BH/#139,
A1-prime, G1 and PSC stay open.
