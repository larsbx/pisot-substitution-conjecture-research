# Ten oriented P packets and their exact physical exits

## Scope and hypotheses

This continues [the H3 carrier](class-a-boundary-h3-carrier-2026-10-27.md).
Work only on the minus boundary: integers k,t>=0,
n=k+t+3, d=2n-1-k, A=n+d=2n+t+2, N=n-1. Actual ordered words are
x -> x y^A x, c -> c y^n x, y -> x y^N c.
A label is (top,bottom,x-coordinate,c-coordinate,y-coordinate), with
bottom-minus-top full Parikh transport. Occurrence ordinals start at zero.
No endpoint contact counts as strict interior overlap.

Normalize Ly=1. Put h=1/beta, alpha=beta-(n+2),
a=Lx=2+alpha-h, b=Lc=1+h, v=alpha+h, w=alpha+2h.
The inherited exact certificates give

    0<h<1/5, 0<alpha<1, 0<v<1, 0<w<1.

The cubic is f(X)=X^3-(n+2)X^2-(t+3)X+2.
Thus beta*alpha=t+3-2h>1, so alpha>h. These are rational/polynomial
identities and inequalities on the unbounded cone, not numerical estimates.
The dependency certificate explicitly replays both v<1 and w<1.

Sources, their normalized shifts s, incidence images Mz, and inflated shifts G=beta*s:

| Packet | Label | s | Mz | G |
| --- | --- | --- | --- | --- |
| P | (y,y,-1,-1,3) | -alpha | (0,2,-t-5) | -t-3+2h |
| Pplus | (y,y,-1,-1,4) | 1-alpha | (1,3,k-3) | k+2+w |
| A2h | (y,y,0,2,-2) | 2h | (0,0,2) | 2 |
| B2h | (y,y,0,2,-3) | -1+2h | (-1,-1,3-n) | 2-beta |
| D | (x,y,1,2,-4) | v | (0,-2,t+6) | t+4-2h |

A2h is a packet name; A without a suffix remains the run length n+d.
All five sources have strict physical interior overlap. Include each actual
orientation reversal R(top,bottom,z)=(bottom,top,-z), with swapped actual
ordinals. These are ten oriented sources, without a reversal quotient.
The [stop/go](class-a-boundary-p-stopgo-2026-10-27.md) preserves the
physical/every-overlap/internal-space distinctions.

## Complete first/run/last tables

For a word with run length R, prefix displacements are 0 at FIRST,
a+i-1 at RUN index 1<=i<=R, and a+R at LAST index R+1.
Its child types are x,y,c for sigma(y), and x,y,x for sigma(x).
For every pair set s'=G+prefix_bottom(j)-prefix_top(i).
The complete test is -length(bottom child)<s'<length(top child).

Every run index below is also clipped to its actual word. In the first four
columns both run bounds are N and LAST=n; for D top run bound is A and
LAST=A+1, bottom run bound N and LAST=n. A dash means empty.

| Kind | P | Pplus | A2h | B2h | D |
| --- | --- | --- | --- | --- | --- |
| FIRST/FIRST | - | - | (0,0) | - | - |
| FIRST/RUN | i=0; t+1<=j<=min(N,t+3) | - | - | (0,N) | - |
| FIRST/LAST | (0,n) iff k=0 | - | - | (0,n) | - |
| RUN/FIRST | - | k+1<=i<=min(N,k+3); j=0 | i=1,2; j=0 | - | i=t+2,t+3,t+4; j=0 |
| RUN/RUN | j-i=t+2,t+3 | i-j=k+2,k+3 | i-j=2 | - | i-j=t+3,t+4 |
| RUN/LAST | max(1,k)<=i<=k+1; j=n | - | - | - | i=n+t+3,n+t+4; j=n |
| LAST/FIRST | - | (n,0) iff t=0 | - | - | - |
| LAST/RUN | - | i=n; max(1,t)<=j<=t+1 | i=n; j=n-2,n-1 | - | - |
| LAST/LAST | - | - | - | - | - |

For run/run impose both actual bounds. In particular a diagonal strip with
no remaining run ordinal is empty. Reversal transposes this table and negates
the full target label; it preserves strict intersection exactly.

Here is the inequality reduction for every nonempty kind and its exclusions:

* **P.** FIRST/RUN has s'=j-t-2+v, giving t+1<=j<=t+3 because
  a-v=2-2h. FIRST/LAST has s'=k+1+v; the upper margin a-s'=1-k-2h
  is positive exactly at k=0. RUN/RUN uses G+j-i and 0<2h<1.
  RUN/LAST has s'=k+2h-i; its lower margin is
  k+1+3h-i and upper margin i-k+1-2h, hence i=k,k+1,
  with i=0 removed. FIRST/FIRST has G+a=v-t-1<0, so lies
  to the left even of the bottom x. RUN/FIRST and LAST/FIRST move
  farther left. LAST/RUN is bounded by G-1<-1 and LAST/LAST by G<-b.
* **Pplus.** RUN/FIRST has s'=k+1+3h-i, giving k+1<=i<=k+3
  using w<1. RUN/RUN has G-i+j and 0<w<1. LAST/FIRST has
  s'=-t-2+3h; its lower margin is w-t, positive exactly at t=0.
  LAST/RUN has s'=j-t-1+w, giving t<=j<=t+1 because b-w=1-v.
  FIRST/FIRST has G-a=k+3h>0; FIRST/RUN and FIRST/LAST increase
  it, so lie past their top child. RUN/LAST has s'>1 and LAST/LAST G>b.
* **A2h.** FIRST/FIRST is interior because 2<a. RUN/FIRST has
  s'=3-a-i, so exactly i=1,2. RUN/RUN is interior only at i-j=2;
  the adjacent diagonals have shifts +1 and -1, which are contacts.
  LAST/RUN has s'=2+j-n, hence j=n-2,n-1 since 1<b<2.
  FIRST/RUN and FIRST/LAST lie past the top child. RUN/LAST has
  s'>=3, LAST/FIRST has lower margin 3-n<=0, and LAST/LAST 2>b.
* **B2h.** FIRST/RUN has s'=j+1-n-h, hence exactly j=N.
  FIRST/LAST has s'=1-h, strictly between -b and a.
  FIRST/FIRST is below -a; RUN/FIRST and LAST/FIRST decrease it.
  RUN/RUN is below -1. RUN/LAST has s'=-alpha-i and lower
  margin 1+h-alpha-i<0 for i>=1 because alpha>h.
  LAST/RUN is still farther left; LAST/LAST G<-b.
* **D.** RUN/FIRST has s'=t+3-v-i; the upper and lower guards give
  t+2<=i<=t+4. RUN/RUN gives i-j=t+3,t+4.
  RUN/LAST has s'=t+n+4-2h-i; its two guards give exactly
  i=n+t+3,n+t+4. These indices are <=A since
  A-(n+t+4)=n-2>0. FIRST/FIRST lies past a since G-a=t+2-v>0,
  and FIRST/RUN and FIRST/LAST increase it. LAST/FIRST lies below
  -a since G<A; LAST/RUN is at most -n-2h<-1;
  LAST/LAST has s'=1-n-2h<-b.

The exact occurrence counts per source (and per reversal) are respectively
2k+4, 2t+4, n+2, 2, 2n+3. Splitting k=0 versus k>=1 and t=0
versus t>=1 evaluates the clipped lengths without a finite parameter ceiling.
Production synthesis follows these strips in O(n+d) time and O(n+d) output
space, rather than enumerating the Cartesian product.

## Full transport and exact outgoing union

For every source z=(x,c,y),

    Mz=(2x+c+y, c+y, (n+d)x+n*c+(n-1)y).

FIRST prefixes have Parikh vector (0,0,0); RUN i has (1,0,i-1),
and LAST has (1,0,R). Add bottom prefix minus top prefix to Mz.
The coefficientwise canonical certificate checks all nine kind identities
on the affine index basis 1,2, for both orientations. It also reduces
beta times the physical field formulas modulo f, after clearing the positive
beta denominator: beta*a=beta^2-n*beta-1, beta*b=beta+1.
A corrupted field identity refuses. These checks certify symbolic identities;
the preceding inequalities prove all guards and exclusions.

The union of target labels over the entire parameter chamber is exactly 51.
Its base-oriented generating list has 31 labels; its intersection with the
reversed list has 11 labels, including the typed coincidence.
This is a chamber-wide union, not a count attained by every member:

| Source | Complete base target labels; y denotes the last coordinate |
| --- | --- |
| P | (x,y,1,2,y), y=-5..-3; (x,c,1,2,-3); (y,y,0,2,y) and (y,c,0,2,y), y=-3,-2 |
| Pplus | (y,x,0,3,y), y=-5..-3; (y,y,1,3,y) and (c,y,1,3,y), y=-6,-5; (c,x,0,3,-5) |
| A2h | (x,x,0,0,2); (y,x,-1,0,y), y=1,2; (y,y,0,0,0); (c,y,0,0,y), y=0,1 |
| B2h | (x,y,0,-1,1); (x,c,0,-1,2) |
| D | (y,x,-1,-2,y), y=3..5; (y,y,0,-2,y) and (y,c,0,-2,y), y=2,3 |

The table gives symbolic containment and the exact finite generating set.
The archived receipt provides an actual k,t,i,j witness for every label,
including reversals, proving attainment. Finite witnesses suffice for this
existential direction; they do not replace the universal guard proof.

## Selected paths, including the two clipped cases

Write C=(y,y,0,0,0). The previously certified suffixes are
K -> L -> H1 -> C at (k+1,0),(0,n-2),(1,2).
Every edge below retains the full target label, literal occurrence and strict
geometry. Reversed paths swap every index and reverse every target.

| Source and range | Selected actual path | Length |
| --- | --- | --- |
| P, k=0 | P --(0,t+2)--> D --(t+2,0)--> K -> L -> H1 -> C | 5 |
| P, k>=1 | P --(1,t+3)--> B2h --(0,N)--> H1 --(1,2)--> C | 3 |
| Pplus, all k,t | Pplus --(k+2,0)--> L -> H1 -> C | 3 |
| D, all k,t | D --(t+2,0)--> K -> L -> H1 -> C | 4 |
| B2h, all k,t | B2h --(0,N)--> H1 --(1,2)--> C | 2 |
| A2h, n>=4 | A2h --(3,1)--> C | 1 |
| A2h, n=3 | A2h --(1,0)--> F --(1,2)--> B2h -> H1 -> C | 4 |

For P at k=0, t+3=n is a real LAST c, not an unavailable ordinal and not
a RUN y. The actual (1,n) target is (y,c,0,2,-3), not B2h.
The universal alternative (0,t+2) reaches D even outside this small-k case.
The run/run shortcut is certified on the shifted cone k=k'+1 only.

For A2h at n=3, necessarily k=t=0, the actual (3,1) target is
(c,y,0,0,0). It is a genuine geometric half-coincidence but not the
stronger typed C terminal. The entire child table proves that no one-step
C exists at n=3. Here n=3,d=5,A=8,N=2 and F=(y,x,-1,0,2).
Its shift is 2-a=-alpha+h in (-1,0), its incidence image is (0,2,-4),
and the actual (1,2) prefixes add (0,0,1), giving B2h.
Its inflated shift is -2+2h, so the child shift is -1+2h in (-1,0).
This is an exact calculation at one integer member, not an extrapolation.
No complete all-chamber star for F is claimed.

For A2h's ordinary terminal the certificate separately checks k=k'+1
and t=t'+1; these cones cover exactly n>=4. In each, the existing indexed
prefix kernel verifies both word bounds. It refuses an attempted all-cone
RUN(3) at N=2, as it should. The finite exceptional path is checked against
the native Perron field and independently against rational root enclosures.

A stage rank exists only on this selected packet: P=5, D=4, K=3,
L=2, H1=1, C=0; Pplus=3, B2h=2; A2h=1 at n>=4 and 4 at n=3,
with exceptional F=3. Reversals inherit the same rank. All selected edges
strictly decrease. The verifier refuses labels outside this packet, a changed
intermediate despite the correct final C, and wrong terminal tile types.

There is also the genuine all-chamber cycle
L --(1,n)--> P --(0,t+2)--> D --(t+2,0)--> K --(k+1,0)--> L.
L has its H1 exit. This prevents a strictly decreasing rank on every edge
of a carrier containing that cycle, and does not give a closed obstruction.

## Exact replay and status

Canonical implementation: `kernel/psc/class_a_boundary_p_children.mojo`.
Driver and native every-pair regression:

```sh
cd kernel
pixi run --locked mojo run -I . class_a_boundary_p_children.mojo
pixi run --locked mojo run -I . tests/test_class_a_boundary_p_children.mojo
```

Native locked Mojo 1.1.0.dev2026090805: 56 members (k=0..7,t=0..6),
86,632 literal ordered pairs, 6,328 accepted, 1,490 selected path edges.
All 51 image labels are attained. Every pair is compared to the independent
canonical word/Parikh/Perron child calculation; every accepted edge is also
checked after actual reversal. Guard corruption, wrong types/indices,
endpoint contact, duplicate synthesis and out-of-packet rank are controls.

Independent Python uses literal word prefixes, integer coordinates modulo the
cubic and Fraction root brackets, with a fixed 512-refinement failure budget.
It covers 117 members (k=0..12,t=0..8), 1,170 source cells,
325,416 ordered pairs, 17,316 accepted and 3,084 selected path edges.

```sh
python -m pytest -q tests/test_class_a_boundary_p_children.py
python oracles/python/class_a_boundary_p_children.py > /tmp/boundary-p.json
cmp /tmp/boundary-p.json evidence/class-a-boundary-p-2026-10-27/probe.json
```

Receipts, source digests and SHA256SUMS are in
`evidence/class-a-boundary-p-2026-10-27/`. The dedicated hosted workflow is
`.github/workflows/class-a-boundary-p.yml`. Applicable exact-head native,
Python, Lean, TLA, source-provenance and evidence-policy gates remain required
for integration; pending is not accepted. No Lean/TLA source or governed claim
status changes. Independent human review remains pending.

The next single unclassified target is E2=(x,x,0,0,2), reached uniformly from
A2h at actual (0,0). In particular P reaches A2h at (1,t+4) when k>=2,
so E2 is not an artificial extension of the packet. The 51-label image has
not been shown forward closed, and F's exceptional path is not a full F star.
No result here covers every relevant cyclic seed-reachable strict zipper,
the plus chambers, the target-aware BH bridge or non-unit internal-space
realization. Universal BH/#139, A1-prime, G1 and PSC remain open.
