# J8: complete k=0 stars and typed completion after every first choice

## Result and current base

J8=(y,x,1,2,-5) and its actual reversal have **2n+4 indexed children at
k=0, and 2n+3 at k>=1**. Their outgoing union over the minus boundary has
**18 full typed labels**. Every actual first choice has a selected typed
coincidence completion within **nine edges**, with nine attained. Selected
source exits have six edges at k=0 and four at k>=1. No shortest-path or
every-continuation termination assertion is made.

The current base is #382 head 526b3dc1ef8dcb914802992a6fee7b3148236c6a:
#385 is merged into that branch and its fresh hosted workflows all pass.
This is not main integration or acceptance of a new head. #386 was closed
unmerged. Carry its D0 packet forward unchanged: the reconstructed tree is
799fcce9ad47ad7906905619c8cf88616342df84, exactly #386's tested tree. Preserve
its receipts and the historical status descriptions rather than rewriting
them. Independent R5/#380, D5/#383 and class-C/#384 work is not imported.
The [stop/go](class-a-boundary-j8-stopgo-2026-10-29.md) reuses the recorded
three-primary-source review; no fresh reading or spectral transfer is claimed.
Independent human review remains pending validation debt.

## Hypotheses, full transport and a new exact separator

Integers k,t>=0, n=k+t+3, d=2n-1-k, A=n+d, N=n-1. The ordered words are
x y^A x, c y^n x, x y^N c. Indices are actual zero-based occurrences;
offsets retain every bottom-minus-top Parikh coordinate. Reversal swaps types
and indices and negates all coordinates. Acceptance is strict
-L(bottom child)<shift<L(top child), using actual child lengths. No tile-length
independence premise is used.

Use inherited exact h=1/beta, alpha=beta-(n+2), rho=alpha-h,
zeta=alpha-2h, v=alpha+h, w=alpha+2h, a=Lx=2+rho, b=Lc=1+h, Ly=1.
The established bounds include 0<h<1/5, 0<zeta<rho<1, 0<v<w<1.
J8 has source shift v-1, strictly between -1 and zero. Its image under
M(x,c,y)=(2x+c+y,c+y,A*x+n*c+N*y) is (-1,-3,4-k). Thus its inflated
shift is G=-k-1-w. Add actual bottom prefix minus top prefix for every child.

The extra LAST/RUN child depends on q=alpha+3h versus one. Put
f(X)=X^3-(n+2)X^2+(n-d-1)X+2 and g(X)=X^2-(n+3)X+3. Exact reduction gives

    (beta+1)*g(beta)=1-k*beta,
    g(beta)=beta*(q-1).

Since beta>n+2>5, all denominators are positive. At k=0 the right side is
one; at k>=1 it is negative. Hence q>1 exactly at k=0, q<1 at k>=1,
and equality never occurs. Also 0<q<1+h<2. This is an integer-polynomial
certificate, not a fitted threshold or an approximate sign.

## All nine occurrence kinds

For the top y parent, FIRST is x with prefix 0, RUN i is y with prefix
(1,0,i-1), and LAST n is c with prefix (1,0,N). Physical prefixes are
0, a+i-1, a+N. The bottom x parent has FIRST x, runs 1..A with the same
run-prefix formula, and LAST A+1 is x with prefix (1,0,A).

| Kind | Complete accepted base pairs |
| --- | --- |
| FIRST/FIRST | (0,0) exactly at k=0 |
| FIRST/RUN | i=0, j=max(1,k)..k+2 |
| FIRST/LAST | none |
| RUN/FIRST | none |
| RUN/RUN | j-i=k+1 or k+2, for every i=1..N |
| RUN/LAST | none |
| LAST/FIRST | none |
| LAST/RUN | i=n, j=n+k+1..n+k+2+[k=0] |
| LAST/LAST | none |

Transpose pairs and reverse full typed targets for the other orientation.
All displayed indices are genuine: the RR maximum j=N+k+2 satisfies
A-j>=2t+4, and the LR maximum satisfies A-j>=2t+2.

* FF has negative shift G. Its lower margin a+G=1-k-3h is positive
  exactly at k=0. The upper guard is automatic.
* FR shift is j-k-3h. Strict lower guard -1 gives j>=k; strict upper
  guard a gives j<k+2+w, hence j<=k+2. Clip to genuine runs j>=1.
* FL shift is A-k+1-3h>a, so disjoint.
* RF lower margin against -a is G-i+1=-k-w-i<0, so disjoint.
* RR shift is j-i-k-1-w. Its strict interval (-1,1) gives exactly
  j-i=k+1,k+2, with no run clipping needed.
* RL has minimum shift d+1-k-w=2t+6-w>1, so disjoint.
* LF lower margin against -a is G-N<0, so disjoint.
* LR shift is j-n-k-1-w. Strict lower guard -1 gives j>=n+k+1;
  upper guard b gives j<n+k+2+q. The separator yields the displayed
  final index, with strict equality excluded.
* LL has shift d-k-w=2t+5-w>b, so disjoint.

At k=0 the four nonempty kinds contribute 1,2,2(n-1),3, totaling 2n+4.
At k>=1 they contribute 0,3,2(n-1),2, totaling 2n+3. Canonical synthesis
streams O(n) accepted indices; exhaustive rectangles are independent tests.

## Chamber image and source aliases

| Kind | Complete base typed targets |
| --- | --- |
| FF | H8=(x,x,-1,-3,4), k=0 ancestry only |
| FR | (x,y,0,-3,r), r=3,4,5; r=3 only at k>=1 |
| RR | R8=(y,y,-1,-3,5), S8=(y,y,-1,-3,6) |
| LR | A8=(c,y,-1,-3,5), B8=(c,y,-1,-3,6), L8=(c,y,-1,-3,7); L8 only at k=0 |

Nine base labels and nine disjoint reversals give 18 labels over the chamber.
The actual two-oriented member image has 16 labels at k=0 and 14 at k>=1,
not a constant 18-label carrier. Exact full transport proves containment;
archived actual k,t,i,j witnesses attain every label. Affine index bases 1,2
and actual last prefixes certify all nine coefficientwise transport identities.

The r=3 FR target is existing D4 and r=5 is existing G5. The r=4 target,
locally P8, is already **reversed L**, with a complete star and two-edge exit.
The helper Y8=(y,x,0,3,-5) is already **reversed G5**, with a five-edge exit.
Reuse their exact full labels, old IDs and path constructors. These aliases
receive no new complete-star or uniform-exit claim.

## Explicit tails and their actual parameter guards

New helper names denote full typed labels, never merely equal field shifts:
C8=(x,c,1,2,-5), Q8=(c,c,1,2,-5), W8=(x,x,0,-3,5),
Z8=(x,x,2,3,-6), D8=(c,c,1,2,-4). The local aliases above are retained
only for readability. T/U and J/K/F4/B2h in this table are inherited families.
The table is stated in the base orientation; transpose/negate for reversal.

| Source and guard | First actual edge and selected suffix | Total edges |
| --- | --- | --- |
| J8, k=0 | FR(0,2)->G5, old G5 suffix | 6 |
| J8, k>=1 | FR(0,k)->D4, old n>=4 D4 suffix | 4 |
| H8, n=3 | FL(0,d+4)->R(U), old one-edge suffix | 2 |
| H8, n>=4 | FR(0,d+4)->R(T), old one-edge suffix | 2 |
| R(L), all k,t | old L constructor | 2 |
| G5/R(G5), all k,t | old G5 constructors | 5 |
| R8, k=0 | FL(0,n)->C8, C8 suffix | 6 |
| R8, k>=1 | FR(0,t+3)->R(K), old K suffix | 4 |
| S8, all k,t | RF(k+1,0)->R(G5), old G5 suffix | 6 |
| A8, k=0 | FL(0,n)->Q8, Q8 suffix | 8 |
| A8, k=1 | FL(0,n)->D8, guarded D8 suffix | 4 |
| A8, k>=2 | RR(1,t+4)->R(P1), old P1 suffix | 4 |
| B8, all k,t | RF(k+1,0)->J8, selected J8 suffix | 7 at k=0, else 5 |
| C8, all k,t | FR(0,k+1)->F4, old F4 suffix | 5 |
| Q8, all k,t | RR(1,k+2)->R8, selected R8 suffix | 7 at k=0, else 5 |
| W8, all k,t | RF(2n,0)->J, old J suffix | 5 |
| Z8, k=0 only | LF(A+1,0)->W8, W8 suffix | 6 |
| D8, k=1 only | RR(t+4,1)->R(B2h), old two-edge suffix | 3 |
| L8, k=0 only | LF(n+1,0)->Z8, guarded Z8 suffix | 7 |

Literal prefix legality and every full target identity are certified on the
disjoint exhaustive regions (k,t)=(0,0), (0,t'+1), (1,t), and (k'+2,t).
This covers the n=3 endpoint separately. The imported D4 suffix is used on
n>=4 in the J8 path; no invalid n=3 shortcut is imported.

All full-cone new source overlaps are exact. H8 has shift -1-w with lower
margin a-1-w=1-3h>0. R8/A8 have shift -w and S8/B8 have shift 1-w.
C8/Q8 have shift v-1, W8 has shift 2-3h with upper margin w>0, Z8 has
shift 1+2alpha+h with upper margin 1-w>0, and D8 has shift v.
The reused R(L) has shift 1-3h, R(G5) has shift -2+3h with lower margin w.
Inherited bounds therefore make each indicated source and target strict.

L8 is different: its shift is 2-w and its upper c-length margin is
b-(2-w)=q-1. Thus it is a physical source **only at k=0**, and is disjoint
at k>=1. Its tail refuses outside k=0 and receives no full-cone uniform-exit
ID. Z8 and D8 remain interior at other k, but their supplied paths are proved
only at k=0 and k=1, respectively, and refuse elsewhere. No missing guard is
silently replaced by an empty tail or a uniform claim.

At k=0, R8's real bottom LAST c yields x/c C8, not the same-offset c/c Q8.
At k=1, A8 yields c/c D8, not same-offset x/x Dxx. At k=0 the nominal
D8 RR(t+4,1) has actual top LAST x, not RUN y. Preserve these actual types.
All have strict geometric counterparts, so equal field shifts cannot repair
an incorrect literal occurrence.

Every accepted J8 child is one of the guarded image cases above, with its
guard implied by its actual occurrence. Its tail has at most eight edges.
Prepending the actual first edge proves the nine-edge selected completion
for every indexed first choice. Nine is attained via A8 at k=0. This proves
neither a shortest path nor termination under every continuation.

## Cycles, escapes and registration scope

The genuine uniform two-cycle is J8(n,n+k+2)->B8(k+1,0)->J8, with the
selected J8 exits still available. Reversal gives the other orientation.
B8 is in the 18-label image, while J8 is outside it by c-coordinate +/-2
versus +/-3, so this cycle also gives an explicit image escape. J8's selected
FR child D4 or G5 escapes the older E7 image. Neither union becomes closed.

E7 RF(2n+5,0)->J8 is an actual RUN/FIRST edge only at t>=3. At t=0,1
the ordinal is unavailable; at t=2 it is actual LAST x, with x/x target
(1,2,-5), not the y/x J8 target sharing its offset. Its uniform source
overlap does not imply uniform E7 ancestry.

S41 stays at 33 complete-star registrations and 35 uniform exits including
C (32 nonterminal stars, eight star gaps, six exit gaps). The restored D0
packet raises E7-image stars 6->8 without changing its eight exits; J8 then
raises those counts to ten stars and ten exits. Twenty-two E7-image labels
still lack registered uniform exits, and general E7 all-child productivity
remains open.

The new 18-label image has two inherited complete stars, R(L) and L, and
16 full-cone uniform exits. Its remaining two labels are L8 and reversal,
whose actual k=0 tails suffice for the all-actual-child result. New uniform
exits are J8 plus eight companion families H8/R8/S8/A8/B8/C8/Q8/W8.
No companion complete stars are supplied. Z8/D8/L8 remain unregistered as
full-cone exit interfaces. All 119 source/candidate/image/old-E7-image rows
are compared individually across native and independent registries.

## Replay and remaining gaps

The matching canonical kernel, driver and contract test are
`kernel/psc/class_a_boundary_j8_children.mojo`,
`kernel/class_a_boundary_j8_children.mojo`, and
`kernel/tests/test_class_a_boundary_j8_children.mojo`. Independent literal-word,
integer-polynomial and Fraction replay lives in the matching Python oracle.

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_j8_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_j8_children.mojo
python -m pytest -q tests/test_class_a_boundary_j8_children.py
python oracles/python/class_a_boundary_j8_children.py > /tmp/j8.json
cmp /tmp/j8.json evidence/class-a-boundary-j8-2026-10-29/probe.json
```

Locked Mojo checks 56 members, 112 stars, 33,096 literal pairs, 2,478
accepted edges, 1,274 source/companion path cells, 5,656 such path edges,
14,434 all-child walk edges and 3,690 guarded full-image tail edges.
Independent replay checks 117 members, 234 stars, 122,616 pairs, 6,804
accepted edges, 2,628 source/companion path cells, 11,502 such edges,
39,762 all-child walk edges and 7,532 guarded full-image tail edges.
Both attain all 18 labels, actual reversal and maximum walk nine. Independent
sign refinement has budget 512 and refuses inconclusively on exhaustion;
canonical machine arithmetic refuses overflow. Finite replay validates the
implementation; the nine-kind and parameter-region arguments supply the
family quantifiers separately.

Controls include corrupt separator/field identities, unavailable occurrences,
true LAST versus false RUN types, x/c versus c/c and c/c versus x/x aliases,
k=0-only disjoint sources, interior but unsupported helper-path parameters,
wrong strict interior targets, duplicate-plus-omitted stars at unchanged
cardinality, altered/truncated walks, unequal-type zero terminals, and
missing/duplicate/corrupted registry rows. Source and exit flags remain separate.

Receipts, dependency snapshot, source and packet digests are in
`evidence/class-a-boundary-j8-2026-10-29/`. Local Lean provisioning and the
isolated proof check still fail before compilation and earn no pass. No full
local suite, fresh hosted acceptance or main integration is claimed. Keep
124 governed claims, 34 named Lean proofs and 325 source openings unchanged.
No formal source or generated ledger/status change. No merge pending required
predecessor and exact-head acceptance.

Next unregistered E7 RF target: (y,x,1,2,-6), actual at index 2n+6 only
on t>=4. Its source shift v-2 has lower margin a+v-2=2alpha>0 throughout
the full cone, but no star or exit is claimed here. General E7 all-child
productivity, forward closure, all-edge descent, all-source strict zipper,
plus/non-unit realization, target-aware BH, universal BH/#139, A1-prime,
G1 and PSC remain open.
