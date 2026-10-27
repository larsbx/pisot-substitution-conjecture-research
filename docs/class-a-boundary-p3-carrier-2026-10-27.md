# P3: a complete actual child star with small endpoint cases

## Hypotheses and scope

Continue [the F-family carrier](class-a-boundary-f-carrier-2026-10-27.md)
under the same [stop/go](class-a-boundary-p3-stopgo-2026-10-27.md).
Use the minus class-A chamber k,t>=0, n=k+t+3, d=2n-1-k,
A=n+d, N=n-1, and exactly the ordered words
x->x y^A x, c->c y^n x, y->x y^N c.
Keep full bottom-minus-top Parikh offsets and actual occurrence indices.
Reversal R(top,bottom,z)=(bottom,top,-z) swaps the actual indices.

Let h=1/beta, alpha=beta-(n+2), a=Lx/Ly=2+alpha-h,
b=Lc/Ly=1+h, and theta=alpha-2h. The inherited exact certificates give
0<h<1/5, alpha<1, 2<a<3 and 0<alpha+2h<1.
The characteristic polynomial is
f(X)=X^3-(n+2)X^2-(t+3)X+2 with n+2<beta<n+3.
Exact reduction gives beta^2*theta=(t+1)*beta-2>0,
so 0<theta<1. This is an integer-polynomial sign proof for the unbounded
chamber, independent of the finite replay.

The source is P3=(x,y,1,3,-4). Its shift is 1+alpha+2h,
with upper interior margin a-(1+alpha+2h)=1-3h>0.
It is E3=(x,x,-1,0,3)'s actual LAST/RUN child
(A+1,A-k-1) throughout the chamber: 1<=A-k-1<=A.
Both full types and offsets, and the reversed ancestry, are checked.
This standalone physical statement supplies no new strict-zipper coverage.

## All nine child kinds

The incidence image is M(P3)=(1,-1,d+4). Put q=d+5.
Its inflated physical shift is G=q+theta. FIRST has prefix 0,
RUN i has prefix a+i-1, and LAST R+1 has prefix a+R.
The top run has length A and the bottom run N. Top LAST is x;
bottom LAST is c. Each child must satisfy the strict inequalities
-length(bottom child)<shift<length(top child).

| Kind | Exact child shift | All admissible actual indices |
| --- | --- | --- |
| FIRST/FIRST | q+theta | none |
| FIRST/RUN | q+theta+a+j-1 | none |
| FIRST/LAST | q+theta+a+N | none |
| RUN/FIRST | q-i-1-h | i=q-2..min(A,q+1), j=0 |
| RUN/RUN | q+theta+j-i | i-j=q or q+1, both true run bounds |
| RUN/LAST | q+theta+N-i+1 | none |
| LAST/FIRST | 3-n-h | (A+1,0) iff n<=5 |
| LAST/RUN | j-n+4+theta | (A+1,j), max(1,n-5)<=j<=n-2 |
| LAST/LAST | 4+theta | none |

For RUN/RUN impose 1<=j<=min(N,A-delta), delta=i-j.
An empty interval supplies no child. Reverse the entire table, types and
indices for R(P3). Here are the strict guard reductions and exclusions:

* FIRST/FIRST exceeds a because q>=10 and a<3. FIRST/RUN and
  FIRST/LAST increase it.
* RUN/FIRST has lower margin q-i+1+theta and upper margin
  i-q+2+h. Since 0<theta<1 and 0<h<1, the integer solutions are
  exactly q-2<=i<=q+1, clipped to A. No geometrically disjoint
  same-type candidate immediately outside that strip is retained.
* RUN/RUN gives -1<q+theta-delta<1, hence delta=q,q+1.
* RUN/LAST is at least 5+theta>1, since i<=A and A=n+d.
  Its top child is y, so it is disjoint.
* LAST/FIRST has lower margin 5-n+theta and upper margin
  n-1+alpha>0. Thus it exists exactly at n=3,4,5. At n=6 its
  lower margin is theta-1<0; a legal endpoint is no longer an overlap.
* LAST/RUN has lower margin j-n+5+theta and upper margin
  n-j-2+h. Therefore n-5<=j<=n-2, clipped to true runs.
* LAST/LAST has shift 4+theta>a, so it is disjoint.

Both RF and LR counts are min(4,n-2); the RR strips have
max(0,n-5) and max(0,n-6) occurrences. Add one LF iff n<=5.
For n=3,4,5 the totals are 3,5,7; for n>=6 the sum is 2n-3.
Consequently **each orientation has exactly 2n-3 ordered strict children**.
The canonical synthesis follows these strips in O(n+d) time/output space;
it does not enumerate the Cartesian word product in production.

## Full transport and the 26-label chamber union

The canonical coefficientwise Q[t,k] certificate checks every kind on
legal affine index bases 1,2 and the actual last prefixes, in both
orientations. It also checks the positive-denominator reductions
beta*a=beta^2-n*beta-1, beta*b=beta+1 and
beta*G=beta^2+(d-n+3)*beta-2 modulo f. A corrupt field identity refuses.
The written guard reductions above establish universal completeness;
finite word enumeration is a separate independent replay.

| Kind | Complete base targets; y denotes the final coordinate |
| --- | --- |
| RF | (y,x,0,-1,y), y=-1..2 |
| RR | (y,y,1,-1,y), y=-2,-1 |
| LF | (x,x,0,-1,4-n), n=3,4,5 |
| LR | (x,y,1,-1,y), y=-2..1 |

These are 13 distinct base labels and 13 disjoint reversals. Exact symbolic
cancellation proves containment; archived actual witnesses attain all 26.
The ten RF/RR/LR base labels already lie in the older
[W/X target envelope](class-a-boundary-w-carrier-2026-10-27.md).
This containment does not imply that their full stars or all exits have
already been classified. The three LF targets are confined to the six
parameter members k+t<=2, rather than being uniform chamber sources.

## Typed exits and the false short path at n=3

Let V=(y,x,0,-1,2), W=(c,x,0,1,-1), Q=(y,x,0,-1,1),
and C=(y,y,0,0,0). The actual RF ordinal d+3=q-2 is always
in the top word, since A-(d+3)=n-3>=0. It gives
P3 --(d+3,0)--> V --(n,0)--> W --(1,0)--> Q --(1,2)--> C.
The last three edges are the existing seed-path suffix, with shifts
1-h, h, -h, 0 and full intended types. This is a uniform four-step exit.

When n>=4 the true RF ordinal d+4 instead gives Q, then C in two steps.
The symbolic word bound is checked on the two shifted cones k>=1 and t>=1,
whose union is exactly n>=4. At k=t=0, d+4=A+1 is LAST x, so the
purported Q target (whose top is y) is false. The canonical path constructor
uses the four-step suffix in that one member and the two-step exit elsewhere.
Reversal swaps every actual pair and reverses every intermediate target.
All steps are additionally checked against the literal words, full Parikh
transport, strict Perron overlap and intended typed packet.

The stage assignment P3/R(P3):4, V/R(V):3, W/R(W):2, Q/R(Q):1, C:0
is defined only on those selected labels. It proves descent along the
selected paths and is refused outside that packet. No all-edge or
forward-closed-carrier rank is asserted.

## Evidence and replay

Canonical modules and tests are kernel/psc/class_a_boundary_p3_children.mojo,
kernel/class_a_boundary_p3_children.mojo and
kernel/tests/test_class_a_boundary_p3_children.mojo.
Use the locked kernel Pixi environment, then run the test and driver with
`pixi run --locked mojo run -I .` from kernel/.
Native replay: 56 members, 33,096 literal ordered pairs, 1,792 accepted
children, 228 selected path edges; all 26 labels attained. Every ordered
pair and every accepted edge's actual reversal is checked.

The independent literal-word/integer-polynomial/Fraction oracle is
oracles/python/class_a_boundary_p3_children.py. Run
`python -m pytest -q tests/test_class_a_boundary_p3_children.py`, then run
the oracle and compare its deterministic output with
[evidence](../evidence/class-a-boundary-p3-2026-10-27/probe.json).
Its 117 members / 234 source cells include 122,616 pairs, 5,382 accepted
children, 472 path edges and actual witnesses for all 26 labels.
This finite evidence is not an extrapolation to the universal table.

Controls include legal but disjoint RF(d+2,0), the n=5/6 LF cutoff,
false n=3 RUN(d+4), a wrong interior target already in the image,
invalid ordinals/orientations/parameters, symbolic identity corruption,
rank escape, changed intermediates and a wrong typed terminal despite zero
final offset. Negative controls must refuse before a contract receipt.

Local scoped Python, Markdown/link/proof-bank checks and full repository
provenance pass. All 18 expected TLA outcomes pass. Local Lean fails before
compilation with `failed to locate application` and receives no proof credit.
The evidence packet records the exact attempts and digests. Fresh exact-head
hosted native, full Python, Lean, TLA, provenance and evidence-policy acceptance
is required before integration. Preserve 124 governed claims, 34 named Lean
proofs and 325 source openings.

## Remaining obstruction and theorem status

The 26-label image is not proved forward closed, and not all its targets
are proved productive here. The next explicit uniform unresolved source is
T=(x,y,1,-1,1), the genuine LR(A+1,n-2) child in every member.
Its shift 2+theta is interior with upper margin h>0. Its complete star
is a concrete symbolic obligation; it is not claimed to be the only
remaining case of the whole research program. The three small LF packets
also remain distinct typed obligations.

The actual F/G2 cycle with an exit is preserved. Neither its existence
nor P3's chosen exit establishes a closed obstruction or universal descent.
All-source strict-zipper coverage, plus chambers, target-aware BH and
non-unit internal-space/return-lattice realization remain separate gaps.
Universal BH/#139, A1-prime, G1 and PSC retain their open statuses.
Independent human review remains pending. No governed claim, Lean/TLA
source or proof inventory is changed.
