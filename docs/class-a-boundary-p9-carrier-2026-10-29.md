# P9 complete stars and completion after every first choice

## Scope and dependency

This packet continues open #391, exact head
92e34bea5bffee8a8523eeda40096b453a435377. Its observed pull-request workflows
remain queued. This is provisional dependency use, not accepted integration.
All predecessor files and evidence remain unchanged; concurrent class-C #392
and independent R5/D5 siblings are not imported. The
[stop/go decision](class-a-boundary-p9-stopgo-2026-10-29.md) precedes new code.

For both actual orientations of P9=(x,y,-1,-4,7), the complete indexed star
has **2n+2+[k>=2]** children. Its chamber-wide image has **24 full typed labels**.
Every actual direct child has a selected typed coincidence completion; the
full walk through that first choice has at most **nine edges**, attained.
This statement concerns a selected continuation after every first choice,
not termination under every continuation. The existing selected P9 exit
remains seven edges at k=0 and six at k>=1; do not duplicate its exit claim.

Canonical Mojo code and a native contract are supplied, but **native replay
is blocked by automatic approval review over telemetry risk even with both
telemetry and crash reporting disabled**. No native certificate execution,
compiler acceptance or driver-registry agreement is credited. The independent
exact replay and the written universal proof below are separate evidence.
The PR stays draft pending native and required dependency/exact-head gates.

## Standing exact geometry

Let k,t be nonnegative integers, n=k+t+3, d=2n-1-k, A=n+d=3n-1-k,
and N=n-1. The actual words are

- x -> x y^A x;
- c -> c y^n x;
- y -> x y^N c.

Indices are zero-based. FIRST has prefix zero; RUN i has prefix (1,0,i-1)
for x and y; their LAST prefixes are (1,0,A) and (1,0,N), with actual
LAST types x and c respectively. Retain bottom-minus-top offsets in all
three integer Parikh coordinates. Reversal swaps types and occurrence
indices and negates the full offset. No tile-length independence is assumed.

Use inherited h=1/beta, alpha=beta-(n+2), rho=alpha-h,
v=alpha+h, w=alpha+2h, q=alpha+3h, with
0<h<1/5, 0<rho<v<w<1. Also q>1 exactly at k=0 and q<1 at k>=1,
with equality excluded by the earlier exact identity
beta*(beta+1)*(q-1)=1-k*beta.
Tile lengths are a=Lx=2+rho, b=Lc=1+h, Ly=1.
A child of types u/v with shift S is strict exactly when -Lv<S<Lu.

The incidence update is
M(r,s,z)=(2r+s+z,s+z,A*r+n*s+N*z).
For P9, M=(1,3,k-6); its source shift is 1-q and its inflated shift
G=k-1+w. Source strictness is inherited from #391. Algebraically,
beta*G=beta^2+(k-n-3)*beta+2 modulo
f(beta)=beta^3-(n+2)*beta^2+(n-d-1)*beta+2=0.
The native certificate expresses this coefficientwise identity and the nine
actual prefix kinds on independent affine bases; no sampled sign is used
as a universal guard.

## All nine occurrence kinds

The top word is x y^A x, the bottom x y^N c. Subtract the top prefix
length from G plus the bottom prefix length. Intersect every range below
with the literal RUN bounds 1<=i<=A, 1<=j<=N.

| Kind | Child types | Exact shift | Strict indexed survivors |
| --- | --- | --- | --- |
| FF | x/x | k-1+w | (0,0), k<=2 |
| FR | x/y | k+j+rho+w | (0,1), k=0 |
| FL | x/c | k+n+rho+w | none |
| RF | y/x | k-i-2+3h | max(1,k-2)<=i<=k, j=0 |
| RR | y/y | k+j-i-1+w | i-j=k or k-1 |
| RL | y/c | k+n-1-i+w | j=n, k+n-1<=i<=k+n+[k=0] |
| LF | x/x | k-A-3+3h | none |
| LR | x/y | k+j-A-2+w | none |
| LL | x/c | k-d-2+w | none |

For FF, the upper bound is k<3-3h, equivalently k<=2; the lower
bound follows from w>0. For FR the upper bound is k+j+w<2,
so k+j<=1, giving exactly k=0,j=1. FL exceeds a since k+n+w>2.
RF's lower inequality gives i-k<w, hence i<=k; its upper inequality
gives k-i<3-3h, hence i>=k-2. RR reduces to
0<k+j-i+w<2, exactly the two displayed integer diagonals.
RL's upper inequality gives i>=k+n-1; its lower inequality is
i<k+n+q, producing the k=0 exception without equality.
Its upper ordinal fits A: A-(k+n+1)=2t+4>=4.

LF lies below -a since S+a=k-A-1+w<0.
LR's lower bound would force j>=A+1-k>N, because
A+1-k-N=d+2-k=2t+7>0. LL has S+b=q-2t-6<0.
These exclusions preserve actual endpoint letters and prefixes.

Each RR diagonal fits the top word since N+k<A. At k=0 the second
has j>=2, giving 2N-1 RR pairs; at k>=1 both give N pairs.
RF contributes min(k,3); RL contributes 2+[k=0]. Including FF and FR:

| k | FF | FR | RF | RR | RL | Total |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 1 | 1 | 0 | 2N-1 | 3 | 2n+2 |
| 1 | 1 | 0 | 1 | 2N | 2 | 2n+2 |
| 2 | 1 | 0 | 2 | 2N | 2 | 2n+3 |
| >=3 | 0 | 0 | 3 | 2N | 2 | 2n+3 |

The canonical constructor streams these strips in output-linear space/time;
it does not enumerate the whole word rectangle. The regression contract
compares the constructor to every literal pair independently. Checked
parameter/count/key arithmetic refuses overflow rather than wrapping.

## Full typed image and all actual tails

Transport each surviving actual prefix as M(P9)+prefix_bottom-prefix_top.
The following twelve base labels and their disjoint reversals form the
24-label chamber union. The guard column describes this P9 ancestry;
a source can have an overlap or exit beyond that ancestry.

| Kind | Full base target | Ancestry | Selected tail length / reused interface |
| --- | --- | --- | --- |
| FF | (x,x,1,3,-6) | k=0 | 6, H9 |
| FF | (x,x,1,3,-5) | k=1 | 4, new W9 (uniform) |
| FF | (x,x,1,3,-4) | k=2 | 2, R(H8) |
| FR | (x,y,2,3,-6) | k=0 | 6, new guarded X9 |
| RF | (y,x,0,3,-5) | k>=1 | 5, R(G5) |
| RF | (y,x,0,3,-4) | k>=2 | 2, existing L orientation |
| RF | (y,x,0,3,-3) | k>=3 | 3 here, R(D4); inherited n=3 path retained |
| RR | (y,y,1,3,-6) | all | 6, R(S8) |
| RR | (y,y,1,3,-5) | all (j>=2 at k0) | 6 at k0, 4 otherwise, R(R8) |
| RL | (y,c,1,3,-7) | k=0 | 7, existing R(L8), guarded |
| RL | (y,c,1,3,-6) | all | 7 at k0, 5 otherwise, R(B8) |
| RL | (y,c,1,3,-5) | all | 8 at k0, 4 otherwise, R(A8) |

All twelve have literal witnesses, independently exported in the packet.
This is not a constant memberwise image: both orientations have 14 labels
at k=0, 12 at k=1 and 14 at k=2 and k>=3. In particular the FR and
extra RL sources never get silently treated as full-cone P9 children.

The maximum tail eight is attained at k=0 through R(A8), reached by
P9's actual (n-1,n) RUN/LAST edge. Thus every indexed first choice has
a selected full walk <=9, and nine is attained. No shortest-path optimality
claim is made. Reversal provides the identical statement in the other
orientation with both indices exchanged.

## New selected paths and their exact legality

W9=(x,x,1,3,-5) has source shift w, so it is uniformly strict.
Its incidence image is (0,-2,n+4-k) and inflated shift t+5-2h.
The genuine RUN/FIRST edge (t+4,0) reaches
B9=(y,x,-1,-2,4). Its shift is -v, and -a<-v<1.
Both ordinal margins are positive throughout the full cone.

B9 is uniformly strict with source shift -v. Its image is
(0,2,k-n-3), inflated shift -t-4+2h. Its actual FIRST/RUN
edge (0,t+4) reaches R(B5)=(x,y,1,2,-3), with shift 1+v.
The strict upper margin is a-(1+v)=1-2h>0; the lower margin
is positive. Reuse R(B5)'s existing two-edge exit. B9 therefore has
three edges and W9 four. Both are new uniform exit interfaces, not stars.
All three integer coordinates and both orientations are symbolically bound
by actual prefix identities in the native certificate source.

X9=(x,y,2,3,-6) has source shift 1+2alpha+h, uniformly strict:
a-(1+2alpha+h)=1-w>0. Its image is
(1,-3,3n+4-2k). On k=0 only, actual LAST/FIRST (A+1,0)
reaches W8=(x,x,0,-3,5), with shift 2-3h and strict x/x overlap.
Reuse W8's five-edge exit, giving six. The full-cone formula for that
actual target is (x,x,0,-3,5-k), so the selected W8 suffix cannot
be extended to k>=1. The hypothetical RUN at A+1 has y/x types;
the actual LAST has x/x. Tests retain this same-offset typed distinction.
X9 gets no uniform exit ID despite its uniform source overlap.

R(L8)=(y,c,1,3,-7) has shift w-2. Its lower margin with c is
w-2+b=q-1, positive exactly at k=0. Reuse the existing guarded seven-edge
tail. It remains disjoint outside k=0 and never gets a uniform exit ID.
Thus all 24 actual image cases are covered by 20 uniform exit labels
and four guarded labels; no empty-tail convention hides an unknown case.

The uniform W9 -> B9 edge leaves the 24-label image (different c-coordinate).
P9's selected H9/R(G5) child leaves the older J9 image. Neither image
is a closed obstruction. No every-continuation termination follows.

## Registry and replay boundaries

P9 keeps existing exit ID62 and newly binds its complete star to ID62.
New W9/B9 exits have IDs64/65. X9 and L8 keep exit zero.
Only the L pair in the new image has an inherited complete star;
no companion complete stars are supplied. The old J9 image gains two
complete stars (P9/reversal), retains only its two registered uniform exits,
and still has 32 exit gaps. S41 stays 33 stars and 35 exits including C.
The new registry driver emits 107 rows: eight source/companion, 41 S41,
24 image and 34 old-J9-image. Parser tests use explicitly synthetic rows;
there is no native-driver receipt until native replay actually succeeds.

Independent exact replay: 117 members, 234 oriented stars, 122,616 literal
pairs, 6,750 accepted edges, 1,422 source-path edges, 1,746 companion-path
edges and 39,618 all-child walk edges. Every image label is witnessed;
actual reversals and typed edges to C are checked. Rational sign refinement
is inherited with budget 512 and raises on exhaustion. Finite replay checks
implementation separately from the universal nine-kind/count/path proof.
See the [replay packet](../evidence/class-a-boundary-p9-2026-10-29/README.md).

All 84 scoped Python tests pass. Provenance and all 18 TLA outcomes pass.
The digest manifest was added after an initial integrity failure; the final
96 recorded-data/link/Markdown-source checks pass, alongside the other
integrity/governance checks.
Native replay, exact-head hosted acceptance and dependency acceptance remain
outstanding. Lean remains a separate pre-compilation toolchain blocker.
No full local suite, independent human review, new companion stars, general
J9/E7 all-child result, forward closure, all-edge rank, all-source strict
zipper, plus/non-unit realization, target-aware BH, universal BH/#139,
A1-prime, G1 or PSC promotion. Governed claims and formal files stay unchanged.
The next complete-star gap is H9=(x,x,1,3,-6), already with a six-edge exit
and actual P9 FIRST/FIRST ancestry at k=0; its source is uniformly strict.
