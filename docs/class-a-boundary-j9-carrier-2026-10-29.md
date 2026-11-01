# J9: complete clipped stars and uniform selected exits

## Result and dependency scope

J9=(y,x,1,2,-6) and its actual reversal have complete indexed stars
throughout the minus class-A boundary. Their outgoing union over the parameter
chamber has **34 full typed labels**. The exact indexed count is piecewise
in m=t-k, stated below. J9 has a selected typed coincidence exit of **eight
edges at k=0 and seven at k>=1**. Two companion families have uniform exits:
P9=(x,y,-1,-4,7) takes seven/six edges, H9=(x,x,1,3,-6) takes six.
No complete companion stars or all-direct-child productivity is supplied.

Base: #382 head d204b822b8912c8d41b7cca22bd7de9770c88e3c, which merges
#387 and therefore carries the previous D0 and J8 packets. Its merge-head
hosted workflows were queued at first inspection; that is not fresh acceptance
or main integration. Preserve predecessor receipts and statuses as historical
records. Independent R5/#380, D5/#383, class-C/#384 and main-only spike repair
#388 are not imported. The [stop/go](class-a-boundary-j9-stopgo-2026-10-29.md)
reuses the recorded three-primary-source actual/every-overlap and non-unit
review; no fresh reading or spectral transfer is claimed. Independent human
review remains pending validation debt.

## Hypotheses and two exact threshold identities

Integers k,t>=0, n=k+t+3, d=2n-1-k, A=n+d, N=n-1. Ordered words are
x y^A x, c y^n x, x y^N c. Every offset retains all bottom-minus-top integer
Parikh coordinates. Indices are actual zero-based occurrences. Reversal
swaps types and indices and negates all coordinates. Strict acceptance uses
-L(bottom child)<shift<L(top child), with actual typed lengths. No tile-length
independence premise is used.

Use inherited exact h=1/beta, alpha=beta-(n+2), rho=alpha-h,
zeta=alpha-2h, v=alpha+h, w=alpha+2h, q=alpha+3h,
a=Lx=2+rho, b=Lc=1+h, Ly=1. Established bounds give 0<h<1/5,
0<zeta<rho<1 and 0<v<w<1. J8's exact certificate gives q>1 exactly at
k=0, q<1 at k>=1, no equality, and 0<q<1+h<2.

J9 has source shift v-2. Its strict lower margin a+v-2=2alpha>0
and upper margin 1-(v-2)>0 prove its full-cone source overlap. Its image
under M(x,c,y)=(2x+c+y,c+y,A*x+n*c+N*y) is (-2,-4,5-n-k), with inflated
shift G=-n-k-3-2v. Exact coefficient identities reduce transport modulo

    f(X)=X^3-(n+2)X^2+(n-d-1)X+2.

The new half threshold is **v>1/2 iff t>=k-2**, with no equality. It follows
without a fitted chamber rule. Put m=t-k and q4=alpha+4h. Exact identities are

    beta*(2v-1)=m+3-q4,
    (beta+1)*(beta^2-(n+3)*beta+4)=2+(1-k)*beta,
    beta^2-(n+3)*beta+4=beta*(q4-1).

The first identity follows from beta*v=t+4-2h and is checked after clearing
another positive beta. Since 0<q4<1+2h<7/5<2, m>=-1 makes its right side
positive and m<=-3 makes it negative. On m=-2, necessarily k>=2. Then
2+(1-k)*beta<=2-beta<0 because beta>n+2>5, so q4<1 and m+3-q4>0.
This covers every parameter case and excludes equality. Write s=1 when
t+2>=k, else s=0, so s<2v<s+1. Put e=1 at k=0, else e=0.

## All nine occurrence kinds and indexed counts

The top y word has FIRST x, RUN i=1..N y with prefix (1,0,i-1), and
LAST n c with prefix (1,0,N). Their physical prefixes are 0, a+i-1, a+N.
The bottom x word has FIRST x, RUN j=1..A y with the same run-prefix
formula, and LAST A+1 x with prefix (1,0,A).

| Kind | Complete accepted base pairs |
| --- | --- |
| FIRST/FIRST | none |
| FIRST/RUN | i=0, j=n+k+2+e..n+k+4+s |
| FIRST/LAST | none |
| RUN/FIRST | none |
| RUN/RUN | j-i=n+k+3+s or n+k+4+s; 1<=i<=min(N,A-(j-i)) |
| RUN/LAST | j=A+1, i=2t+2-s..min(N,2t+4) |
| LAST/FIRST | none |
| LAST/RUN | i=n, j=2n+k+4..min(A,2n+k+5) |
| LAST/LAST | (n,A+1) exactly when -1<=m<=2 |

Transpose actual pairs and reverse full targets for the other orientation.
Empty strips contribute no edges; endpoints are never fictitious RUN letters.

* FF has shift G<-a and is disjoint.
* FR shift is j-n-k-2-q. Its lower guard -1 gives j>=n+k+2+e;
  upper guard a gives j<n+k+4+2v, hence j<=n+k+4+s.
  These are genuine runs because A-(n+k+4+s)=2t+1-s>=0.
* FL shift is 2t+4-q>a: its upper margin would be 2(v-t-1)<0.
* RF lower margin against -a is G-i+1<0, so disjoint.
* RR shift is j-i-n-k-3-2v. The strict interval (-1,1) gives exactly
  the two displayed differences, clipped to both actual runs.
* RL shift is 2t+3-2v-i. Upper guard 1 gives i>=2t+2-s. Lower
  guard -a gives i<2t+5-q: its integer upper bound is 2t+4 at k>=1
  and 2t+3 at k=0. At k=0, the latter exception is absorbed by i<=N:
  only t=0,1 can have any RL edge, and their N is below both bounds.
* LF lower margin against -a is G-N<0, so disjoint.
* LR shift is j-2n-k-3-2v. Its lower guard -1 gives
  j>=2n+k+3+s. Literal j<=A requires m>=1+s. The s=0 region has
  m<=-3 and cannot satisfy that bound. Hence all accepted LR edges have
  s=1, m>=2; there 1<2v+h<2, making the strict upper guard b equivalent
  to j<=2n+k+5. No extra threshold on 2v+h is needed.
* LL shift is m-2v. Its lower margin a+m-2v=m+2-q is positive
  exactly at m>=-1: the borderline m=-1 forces k>=1 and q<1.
  Its upper margin b-m+2v=1-m+2v+h is positive exactly through m=2;
  at m=2, s=1 supplies 2v+h>1, while m>=3 fails because 2v+h<2.

FR has 3+s-e occurrences. RR contributes
min(N,2t+2-s)+min(N,2t+1-s). RL contributes its clipped displayed interval.
LR has one occurrence at m=2 and two at m>=3; LL contributes one on
-1<=m<=2. Summing gives the following exact count per orientation:

| Parameter region | Indexed children |
| --- | --- |
| m<=-3 | 4t+9 |
| m=-2 | 2n-1 |
| m=-1 | 2n+1 |
| m>=0 | 2n+min(m,2)+2-e |

For m<=-3 both RR lengths are below N, and RL has three occurrences.
For -2<=m<=1, RR has 2N+2m-3 occurrences and RL has 2-m.
For m>=2, RR has 2N and RL is empty. These substitutions prove the sum,
including t=0 empty second strips. Canonical synthesis streams O(n+t)
accepted strips rather than scanning the word rectangle; the rectangle is a test.

Equal counts do not identify stars. At (k,t)=(t+2,t), the high half has
FR target (x,y,-1,-4,9), while the low member (t+3,t) has the RR target
(y,y,-2,-4,8); each star has 4t+9 occurrences. Each displayed source is
disjoint in the opposite half. The separator, not matching counts, chooses edges.

## Exact typed image

Add actual bottom prefix minus top prefix to (-2,-4,5-n-k). Coefficientwise
identities check every kind on affine index bases 1,2 and actual last prefixes;
the exact geometric affine recurrence is reduced modulo the same cubic.

| Kind | Complete base targets over the chamber |
| --- | --- |
| FR | (x,y,-1,-4,r), r=6..9 |
| RR | (y,y,-2,-4,r), r=8..10 |
| RL | (y,x,-2,-4,r), r=7..10 |
| LR | (c,y,-2,-4,r), r=9,10 |
| LL | (c,x,-2,-4,r), r=7..10 |

Seventeen base labels and seventeen disjoint reversals give 34 labels.
The guards and exact cancellation prove containment; archived actual k,t,i,j
witnesses attain every label. This is a chamber-wide union, not a constant
memberwise image or uniform physical carrier. For example the two-oriented
image has 14 labels at (0,0) and 16 at (3,0). Opposite-half disjoint targets
remain explicit and are not assigned uniform source/tail interfaces.

## Uniform selected exits and the true k=0 endpoint

The source path begins with the actual FR(0,n+k+3) child
P9=(x,y,-1,-4,7) for every k,t. This index is a genuine run with room
A-(n+k+3)=2t+2. P9's source shift is 1-q, strictly between -1 and a
throughout the full cone, since 0<q<1+h<2 and h<1/5.
H9=(x,x,1,3,-6) has source shift w-1 strictly between -1 and zero.

| Source and guard | Actual first edge and existing suffix | Total edges |
| --- | --- | --- |
| J9, k=0 | FR(0,n+k+3)->P9, selected P9 suffix | 8 |
| J9, k>=1 | same first edge, selected P9 suffix | 7 |
| P9, k=0 | FF(0,0)->H9, selected H9 suffix | 7 |
| P9, k>=1 | RF(k,0)->R(G5), existing five-edge suffix | 6 |
| H9, all k,t | FR(0,k+1)->G5, existing five-edge suffix | 6 |

G5=(x,y,0,-3,5) and its actual reversal retain their existing identities,
IDs and certificates. Their source shift is 2-3h with positive upper margin w.
No new complete companion star or replacement G5 claim is made.

Literal prefix legality and every full target identity are certified on the
full cone for the J9/H9 transitions, the k=0 ray n=t+3,d=2t+5 for P9's
FIRST/FIRST edge, and the shifted k=k'+1 cone n=n'+1,d=d'+1 for its RUN.
At k=0, ordinal k is FIRST x with zero prefix; the nominal RF(k,0)->R(G5)
would use both the wrong y type and the wrong run prefix (1,0,-1).
Its real target is H9, not R(G5). Preserve the true entire label and prefix.

The two P9 orientations are the only image labels with registered uniform
tails here. Thirty-two other labels have no registered uniform tails; no
claim that they are unproductive follows. Source productivity alone does not
prove productivity after every possible first choice. The registered-tail
interface refuses unsupported labels even when their physical sources are interior.

P9's first selected child is H9 or R(G5), outside the 34-label image by
c-coordinate +/-3 versus +/-4, so the image has a uniform explicit escape.
Every J9 image label leaves the older E7 image, whose c-coordinate is +/-2.
Preserve the predecessor J8/B8 and D0 cycles with exits. No closed obstruction,
all-edge descent or every-continuation termination is inferred.

## Ancestry, registration and replay

E7's proposed RF(2n+6,0) reaches J9 only at t>=4. At t<=2 it is unavailable;
at t=3 it is actual LAST x with x/x target (1,2,-6), sharing the offset
but not the full typed label of J9. Symbolic legality is certified only on
t=t'+4, n=n'+4, d=d'+8. A uniform J9 source overlap is not uniform ancestry.

S41 stays at 33 registered stars and 35 uniform exits including C, with eight
star gaps and six exit gaps. E7's image rises 10->12 complete stars and
10->12 uniform exits, leaving 20 exit gaps. The new image has zero registered
complete stars and two uniform exits. J9 gains stars/exits; P9/H9 gain exits
without complete stars. All 113 source/candidate/image/E7-image registry rows
are compared individually by the independent implementation. No sibling
classification is counted or governed status promoted.

Canonical kernel, driver and contract test are the matching
`kernel/psc/class_a_boundary_j9_children.mojo`,
`kernel/class_a_boundary_j9_children.mojo`, and
`kernel/tests/test_class_a_boundary_j9_children.mojo`.

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_j9_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_j9_children.mojo
python -m pytest -q tests/test_class_a_boundary_j9_children.py
python oracles/python/class_a_boundary_j9_children.py > /tmp/j9.json
cmp /tmp/j9.json evidence/class-a-boundary-j9-2026-10-29/probe.json
```

Locked Mojo 1.1.0.dev2026090805 checks 56 members, 112 stars, 33,096 literal
pairs, 2,130 accepted edges, 336 source/companion path cells, 2,156 such path
edges and 686 registered image-tail edges. Independent literal-word,
integer-polynomial/Fraction replay checks 117 members, 234 stars, 122,616
pairs, 5,390 accepted edges, 702 source/companion cells, 4,482 such edges
and 1,422 registered image-tail edges. Both attain all 34 labels and verify
actual reversal. Finite replay validates implementation separately from the
universal nine-kind, separator and selected-exit argument above. Independent
sign refinement has budget 512 and refuses inconclusively on exhaustion.
Canonical checked arithmetic refuses overflow, including a dedicated control
where A fits but 2n+k+5 would not; no wrapped upper bound can decide a guard.

Controls retain true FIRST/LAST letters, opposite-half disjoint sources and
equal-count differences, corrupt separator/field identities, bad parameters,
ordinals and orientations, wrong strict interior targets, duplicate-plus-omitted
stars at unchanged cardinality, altered/truncated paths, unequal-type zero
terminals, unknown image tails and missing/duplicate/corrupted registry rows.
No blanket all-image uniform-overlap claim is made.

Receipts, dependency snapshot, source and packet digests live under
`evidence/class-a-boundary-j9-2026-10-29/`. Local Lean still fails before
compilation and earns no pass. No full local suite or fresh hosted acceptance
is claimed. Keep 124 governed claims, 34 named Lean proofs and 325 source
openings unchanged, without editing formal sources or generated ledger/status.
Independent human review stays pending validation debt. No merge pending
predecessor and exact-head acceptance.

Next complete-star gap: P9=(x,y,-1,-4,7), now with uniform seven/six-edge
selected exits and uniform actual J9 ancestry FR(0,n+k+3). Every-direct-child
productivity for J9/P9, general E7 productivity, forward closure, all-edge
rank, all-source strict zipper, plus/non-unit realization, target-aware BH,
universal BH/#139, A1-prime, G1 and PSC remain open.
