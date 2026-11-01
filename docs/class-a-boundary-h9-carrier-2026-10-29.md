# H9 complete stars and completion after every first choice

## Scope and dependency

Continue from #391 merge revision65e7b8a8724b9e3f4f6f0ec2f230b3dada4993ca,
which incorporates #393. The observed merge-head hosted runs are queued;
a merge into this stacked branch is not main integration or fresh acceptance.
Every predecessor source and receipt remains unchanged. Concurrent class-C
#392/#394 and independent R5/D5 sibling results are not imported. The
[stop/go note](class-a-boundary-h9-stopgo-2026-10-29.md) precedes new code.

H9=(x,x,1,3,-6) and its actual reversal have complete indexed stars of
**2A+3 at k=0,1**, and **2A-2k+5 at k>=2**. Their chamber-wide image has
**20 full typed labels**, all with uniform selected exits. Every actual
first choice has a selected typed coincidence completion within **seven
edges**, attained. Keep the inherited six-edge source exit and ID63.
No termination under every continuation or forward closure is inferred.

## Standing exact ordered geometry

Integers k,t>=0; n=k+t+3, d=2n-1-k, A=n+d=2k+3t+8, N=n-1.
The exact ordered words are x->x y^A x, c->c y^n x, y->x y^N c.
Keep bottom-minus-top integer Parikh offsets in all three coordinates and
zero-based actual occurrence indices. Reversal swaps types and indices and
negates the full offset. No tile-length independence is assumed.

Reuse inherited h=1/beta, alpha=beta-(n+2), rho=alpha-h,
v=alpha+h, w=alpha+2h; 0<h<1/5 and 0<rho<v<w<1.
Lengths are a=Lx=2+rho, b=Lc=1+h, Ly=1.
A u/v child with shift S is strict exactly when -Lv<S<Lu.
These are exact inherited algebraic inequalities, not floating estimates.

The incidence update is
M(r,s,z)=(2r+s+z,s+z,A*r+n*s+N*z).
H9 has source shift w-1, uniformly strict x/x, M=(-1,-3,5-k),
and inflated shift G=-k-w. The native certificate binds
beta*G=-beta^2+(n+2-k)*beta-2 modulo the incidence cubic
beta^3-(n+2)*beta^2+(n-d-1)*beta+2=0.
It binds all nine actual prefix kinds on independent affine run bases;
checking those coefficients leaves k,t symbolic, not finitely sampled.

For each x parent, FIRST0 is x with prefix0; RUN i=1..A is y with
prefix(1,0,i-1); LAST A+1 is x with prefix(1,0,A).
The physical RUN prefix is a+i-1 and LAST prefix a+A.

## Complete nine-kind reduction

Apply S=G+bottom-prefix-top-prefix and intersect with literal run bounds.

| Kind | Types | Exact shift | Strict survivors |
| --- | --- | --- | --- |
| FF | x/x | -k-w | (0,0) iff k<=1 |
| FR | x/y | j-k+1-3h | i=0, max(1,k-1)<=j<=k+1 |
| FL | x/x | A+a-k-w | none |
| RF | y/x | -k-i-1-rho-w | none |
| RR | y/y | j-i-k-w | j-i=k or k+1 |
| RL | y/x | A-i+1-k-w | j=A+1, A-k<=i<=min(A,A-k+2) |
| LF | x/x | -k-w-a-A | none |
| LR | x/y | j-A-k-1-w | none |
| LL | x/x | -k-w | (A+1,A+1) iff k<=1 |

FF/LL require k<a-w=2-3h, exactly k<=1, with no equality.
FR's lower inequality gives j-k>-2+3h, hence j-k>=-1;
its upper inequality gives j-k<1+w, hence j-k<=1.
The upper run ordinal k+1 fits A with margin k+3t+7>0.
FL has S-a=A-k-w>0. RF has S+a=1-k-i-w<0.
RR's interval -1<j-i-k-w<1 gives exactly the displayed two diagonals.
RL's upper inequality forces i>=A-k, and its lower inequality forces
i<A-k+3-3h, hence i<=A-k+2, with actual clipping at A.
LF has S+a=-k-w-A<0. LR has S<=-1-w<-1. These exhaust all kinds.

Both RR diagonals have positive length because A-k>=8. Their counts are
A-k and A-k-1. FR contributes1/2/3 at k=0/1/>=2, as does RL.
FF and LL each contribute one at k<=1. Thus:

| k | FF+LL | FR | RR | RL | Indexed total |
| --- | --- | --- | --- | --- | --- |
| 0 | 2 | 1 | 2A-1 | 1 | 2A+3 |
| 1 | 2 | 2 | 2A-3 | 2 | 2A+3 |
| >=2 | 0 | 3 | 2A-2k-1 | 3 | 2A-2k+5 |

FF and LL have identical prefixes on both sides and therefore the same
full target (-1,-3,5-k), with x/x types. They remain **different indexed
edges**. Replacing LL by another FF preserves cardinality and the set of
labels but violates the star contract. Native and independent checks reject it.
The constructor streams the surviving strips in output-linear work; checked
count arithmetic refuses overflow before allocation. In particular A can fit
while 2A+3 overflows, witnessed at k=0,t=2000000000000000000.

## Chamber-wide image and existing aliases

Transport all accepted prefixes to full typed labels. The ten base labels
below and their disjoint reversals form the 20-label chamber union.

| Kind | Base targets | H9 ancestry | Selected tail lengths |
| --- | --- | --- | --- |
| FF/LL | (x,x,-1,-3,5) | k=0 | 4, R(W9) |
| FF/LL | (x,x,-1,-3,4) | k=1 | 2, H8 |
| FR | (x,y,0,-3,3) | k>=2 | 3 here, D4 |
| FR | (x,y,0,-3,4) | k>=1 | 2, existing L orientation |
| FR | (x,y,0,-3,5) | all k | 5, G5 |
| RR | (y,y,-1,-3,5) | all k | 6 at k0, 4 otherwise, R8 |
| RR | (y,y,-1,-3,6) | all k | 6, S8 |
| RL | (y,x,-1,-3,4) | k>=2 | 4, new K9 |
| RL | (y,x,-1,-3,5) | k>=1 | 3, new L9 |
| RL | (y,x,-1,-3,6) | all k | 6, new M9 |

Member images are smaller: both orientations have10 labels at k=0,
14 at k=1 and16 at k>=2. All20 chamber labels have actual witnesses in
probe.json. Equal indexed counts do not determine the image: members
(k,t)=(0,1) and(2,0) both have25 edges per orientation but different indexed
stars and base images of five/eight labels respectively.

Every actual tail in the table has at most six edges. D4's inherited
seven-edge n=3 tail remains intact and is replayed as a valid uniform
image-source interface. But D4 is an actual H9 child only at k>=2,
so n>=5 and its three-edge suffix applies. No false full-cone six-edge
bound on arbitrary image-source tails is claimed. Every actual first choice
therefore admits a full walk of at most seven edges. RR(1,2) at k=0 reaches
S8 with its six-edge suffix, attaining seven. No optimality claim is made.

## Three new uniform companion exits

Let K9/L9/M9=(y,x,-1,-3,r), r=4/5/6, with source shifts r-5-w.
All are uniformly strict y/x: K9's lower margin is a-1-w=1-3h>0,
L9's is a-w=2-3h>0, and M9's upper margin is w>0.
Their incidence images are respectively
(-1,1,k-2n-3), (0,2,k-n-4), (1,3,k-5).
The canonical source binds these full images, Perron-field multiplication
and both orientations of every actual prefix transition.

K9 has inflated shift -beta*(1+w). Its actual FIRST/RUN(0,d+3)
edge reaches V=(x,y,0,1,-2), shift b-2=-1+h, strictly between -1 and a.
The run index fits with A-(d+3)=n-3>=0, including the floor where it is
still the final RUN y. Reuse V's existing three-edge suffix: K9 takes four.
The tempting next ordinal d+4 is actual LAST x at n=3, giving
(x,x,0,1,-1), not fictitious RUN target (x,y,0,1,-1), despite equal offsets.
Both are strict sources; native and independent controls retain the type distinction.

L9 has inflated shift -t-5+2h. Actual FIRST/RUN(0,t+5) reaches
R(B5)=(x,y,1,2,-3), shift 1+v. Its strict upper margin is
1-2h>0. The index has A-(t+5)=2k+2t+3>0. Reuse the existing two-edge
suffix: L9 takes three.

M9 has inflated shift k+w. Actual RUN/FIRST(k+1,0) reaches
R(G5)=(y,x,0,3,-5), shift w-a=-2+3h, with strict lower margin w>0.
The top y run fits because N-(k+1)=t+1>0. Reuse the existing five-edge
suffix: M9 takes six. These simple uniform selected paths are not claimed
shortest. There are no new companion complete stars.

K9->V uniformly leaves the 20-label image by c-coordinate1 versus+/-3;
its H9 ancestry begins at k>=2. This is an explicit image escape, not a
closed obstruction. H9's source itself is outside the image.

## Reconciliation, finite replay and remaining scope

Keep H9's uniform exit ID63 and newly bind its complete star to ID63.
K9/L9/M9 gain uniform exit IDs66/67/68. S41 stays33 registered stars and35
exits including C. The new image has two inherited L stars and all20 exits,
up from14 exits before this packet. The older P9 image gains two H9 stars,
from2 to4; its20 uniform exits and four conditional tails stay unchanged.
The registry driver exports93 independently checked rows: eight sources,
41 S41,20 new-image and24 P9-image rows. No independent sibling is counted.

Native finite replay checks56 members/112 stars/82096 literal pairs/5124
accepted edges,672 source-path edges,1456 companion-path edges,30366
all-child walk edges and4404 uniform image-tail edges. Independent replay
checks117 members/234 stars/297648 pairs/13302 accepted,1404 source-path
edges,3042 companion-path edges,78714 all-child walk edges and9170 image-tail
edges. Both attain all20 labels and max7, verifying actual reversal and every
full typed intermediate edge to C. Finite replay checks implementation;
the universal nine-kind/count/path arguments above supply the parameter quantifiers.
Independent rational sign refinement has budget512 and refuses inconclusively.
Canonical checked machine arithmetic refuses overflow.

All 94 scoped Python tests and 156 integrity/source/proof-bank/governance
tests pass. Provenance and source/packet digests pass.

See the [replay packet](../evidence/class-a-boundary-h9-2026-10-29/README.md)
for commands, receipts, source/packet hashes and acceptance limits. Telemetry
and crash reporting remain disabled in every native invocation and workflow.
All formal/generated/governed surfaces remain unchanged:124 claims,34 named
Lean proofs,325 source openings. The earlier18 TLA outcomes and Lean
pre-compilation failure remain dependency receipts, not fresh passes.

No companion stars, termination under every continuation, general P9/J9/E7
closure, all-edge rank, all-source strict zipper, plus/non-unit realization,
target-aware BH, universal BH/#139, A1-prime, G1 or PSC promotion.
Required predecessor and fresh exact-head hosted acceptance remain open;
independent human review remains separate validation debt. No merge.
Next complete-star gap: W9=(x,x,1,3,-5), already with a four-edge exit,
and actual H9 FF/LL ancestry in reversed orientation at k=0.
