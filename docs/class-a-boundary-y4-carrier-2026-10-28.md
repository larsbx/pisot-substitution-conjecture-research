# Y4: complete stars and typed tails through every first choice

## Scope and inherited hypotheses

Continue #378 at 4bdacc0dd5618e895351dcf372b071c9560cc582, preserving
all predecessor sources and evidence. Classify Y4=(x,y,1,0,-1) and its true
reversal throughout the minus class-A boundary chamber. Its own two-edge
exit is already certified. The new result supplies a uniform typed tail for
every indexed direct child, including the previously unregistered T2 exit.
This is a one-parent all-child result, not forward closure or universal BH.
Independent human review remains pending; required exact-head hosted gates
remain necessary for integration in stack order. No governed/formal-source
status changes. The [stop/go](class-a-boundary-y4-stopgo-2026-10-28.md)
reuses the existing three-primary-source actual/every-overlap and non-unit review.

Keep k,t>=0, n=k+t+3, d=2n-1-k=k+2t+5, A=n+d=2n+t+2 and N=n-1.
Ordered words are x->x y^A x, c->c y^n x, y->x y^N c. Offsets retain
all bottom-minus-top integer Parikh coordinates in the (x,c,y) basis.
Occurrences are zero-based; strict intersection means
-L(bottom child)<s<L(top child). Actual reversal transposes types and
occurrence indices and negates every coordinate.

Use inherited h=1/beta, alpha=beta-(n+2), rho=alpha-h,
zeta=alpha-2h, a=Lx=2+rho, b=Lc=1+h, Ly=1 and z=alpha+h.
Certified bounds include 0<h<1/5, 0<zeta<rho<1 and 0<alpha+2h<1.
In particular 0<z<1. No decimal root approximation or tile-length independence
assumption is introduced.

## Source transport, uniform ancestry and two-edge exit

Y4 has physical shift a-1=1+rho, with upper margin 1 and positive lower
margin a>0. For M(p,q,r)=(2p+q+r,q+r,A*p+n*q+N*r),

    M(Y4)=(1,-1,d+1),
    G=d+2+zeta,
    beta*G=beta^2+(d-n)*beta-2.

The canonical Q[t,k] certificate compares a generic full incidence image
with a separately supplied expected image, then verifies beta times every
source field element modulo the characteristic cubic. All nine typed Y4
prefix formulas are checked separately from strict guard rounding.

There is uniform actual ancestry through existing T=(y,x,0,-1,1):
T(0,1)->Y4. M(T)=(0,0,-1), and bottom RUN prefix (1,0,0) gives
(1,0,-1), with actual FIRST x/RUN y types. Its target shift a-1 is strictly
below a. This ancestry includes n=3, unlike the earlier R4->D4->Y4 route,
which remains valid only on t>=1.

The existing selected exit is Y4(d+1,0)->T(1,2)->C. The first target shift
is -h in (-a,1), and d+1<=A because n>=3. Reversal preserves both
occurrences and the typed terminal C=(y,y,0,0,0).

## Complete nine-kind strict guard table

Top FIRST/RUN/LAST starts are 0,a+i-1,a+A with 1<=i<=A. Bottom starts
are 0,a+j-1,a+N with 1<=j<=N. Top LAST is x, bottom LAST is c.

| Kind | Full typed child | Shift s | Accepted actual indices |
| --- | --- | --- | --- |
| FIRST/FIRST | (x,x,1,-1,d+1) | G | none |
| FIRST/RUN | (x,y,2,-1,d+j) | G+a+j-1 | none |
| FIRST/LAST | (x,c,2,-1,A) | G+a+N | none |
| RUN/FIRST | (y,x,0,-1,d+2-i) | d+1-h-i | i=d..d+3, j=0 |
| RUN/RUN | (y,y,1,-1,d+1+j-i) | G+j-i | i-j=d+2,d+3; 1<=j<=A-(i-j) |
| RUN/LAST | (y,c,1,-1,A+1-i) | A+2+zeta-i | none |
| LAST/FIRST | (x,x,0,-1,1-n) | -n-h | none |
| LAST/RUN | (x,y,1,-1,j-n) | j-n+1+zeta | i=A+1, j=n-2,n-1 |
| LAST/LAST | D5=(x,c,1,-1,0) | 1+zeta | (A+1,n) |

RR's bottom bound N is automatic: A-(d+2)=n-2 and A-(d+3)=n-3,
both at most N. The second strip is empty at n=3. Every displayed index
retains its literal FIRST/RUN/LAST kind.

The exact guard reductions and exclusions are:

* G>=d+2>=7>a, so all FIRST cases are disjoint. Adding a bottom prefix
  increases the shift.
* RF gives d-h<i<d+3+zeta. Since 0<h<1 and 0<zeta<1, the integers
  are exactly d,d+1,d+2,d+3. They are all true RUNs since A-(d+3)=n-3>=0.
* RR gives d+1+zeta<i-j<d+3+zeta, hence d+2,d+3. The two strip
  counts are n-2 and n-3, respectively.
* RL has minimum shift 2+zeta>1 even at i=A, so it fails the top y bound.
* LF has lower margin a-n-h=2-n+zeta<0, since n>=3 and zeta<1.
* LR gives n-2-zeta<j<n+1+h. Intersecting with 1..N gives exactly
  j=n-2,n-1, both true RUNs even at n=3.
* LL has upper margin a-(1+zeta)=b>0 and a positive lower margin.

Thus every orientation has exactly

    4 + (n-2) + (n-3) + 2 + 1 = 2n+2

strict child occurrences. At n=3, the nominal first pair of the second RR
strip, (d+4,1), is (A+1,1): top LAST x, not RUN y. Its actual child is
R4, with the same offset as R(T2) but a different top type. It is still
strictly interior. Reject the false RR type without deleting that LR event.
The canonical certificate checks the second RR representative only on the
shifted k/t cones covering n>=4. Synthesis streams two O(n) strips and
fixed endpoints; the regression independently checks every O(n^2) literal pair.

## Exact 18-label image and every direct child's tail

The union consists of these nine base labels and their distinct reversals,
for eighteen total labels. It is a chamber-wide union; R(T2) is absent at n=3.
Every label is attained at an actual finite member recorded in the probe.

| Event | Base target | Uniform tail bound to C |
| --- | --- | --- |
| RF | V=(y,x,0,-1,2) | 3, existing W suffix |
| RF | T=(y,x,0,-1,1) | 1 |
| RF | B3=(y,x,0,-1,0) | 2 |
| RF | B4=(y,x,0,-1,-1) | 5 |
| RR | R(T1)=(y,y,1,-1,-1) | 5, existing W suffix reversed |
| RR | R(T2)=(y,y,1,-1,-2) | 7, new selected T2 exit reversed |
| LR | R4=(x,y,1,-1,-2) | 4 |
| LR | R5=(x,y,1,-1,-1) | 3, new |
| LL | D5=(x,c,1,-1,0) | 1, new |

Image containment follows by substituting the complete accepted indices in
the table. Uniform RF representatives, both LR targets and the first RR
representative are checked symbolically on the full cone; the second RR
representative uses the exact n>=4 shifted cones. The explicit image list
and fixed scalar membership predicate agree in regression.

Every row has a uniform typed tail, and its actual reversal has the reversed
tail. Therefore for every k,t and **every indexed strict direct Y4 child**,
there is a typed tail to C of length at most seven. Appending that chosen
first edge gives a complete walk of length at most eight. The tail dispatch
is total on the exact eighteen-label image and refuses targets outside it.
This covers all actual first choices, not just all distinct labels in a sample.
The finite regression constructs and verifies the entire walk for every
accepted occurrence.

The eight-edge bound is attained by the chosen paths, for example through
R(T2) at k=0,t=1. It is not a claim that every chosen path is shortest.
The existing two-edge source exit is preserved.

## New R5 and D5 exits: actual bottom types matter

R5=(x,y,1,-1,-1) has shift zeta in (0,1), image (0,-2,t+3) and
inflated shift t+1-2h. Its actual RR(t+1,1) child is R(B2h)=(y,y,0,-2,3),
with shift 1-2h in (0,1). Both indices are true RUNs throughout the cone.
Reuse R(B2h)->R(H1)->C, giving R5 a uniform three-edge exit.

R5 has the same offset as existing D3, but its bottom parent is y rather than
c. The actual bottom RUN prefix is (1,0,0), not (0,1,0). Consequently this
edge is R(B2h), not D3's P0. Matching the source's field shift does not
supply a typed child identity.

D5=(x,c,1,-1,0) has shift 1+zeta=a-b, image (1,-1,d) and inflated
shift d+1+zeta. Its actual RR(d+1,1) child has full offset (0,0,0) and
both child types y. Hence it is typed C in one edge, throughout k,t>=0.
The bounds A-(d+1)=n-1>=2 and n>=3 make both ordinals true RUNs.
This is a literal prefix cancellation, without a length-independence premise.
D5's offset matches R3's, but its bottom parent c changes the prefix and
allows this direct typed coincidence.

No complete R5 or D5 star is supplied in this increment.

## T2's uniform selected exit closes the registered exit gap

T2=(y,y,-1,1,2) already has its complete star certified. Its source shift is
1-zeta in (0,1), image (1,3,k-1), and inflated shift k+4+alpha+2h.
The new proof supplies one uniform selected exit, not productivity of every
T2 child.

At t>=1, the true RF(k+3,0) child is M5=(y,x,0,3,-3), of shift 3h.
The index is a true RUN because N-(k+3)=t-1>=0. M5's source is strict
since 3h<1. It has RF(2,0)->F0=(y,x,-1,0,2), of shift -rho in (-1,0).
F0 then has FR(0,t+1)->D=(x,y,1,2,-4), of shift z in (0,1). Its bottom
RUN is legal because A-(t+1)>=0. Reuse the existing four-edge
D->K->L->H1->C suffix. Thus F0 has a five-edge exit, M5 six, and T2 seven.

At t=0, k+3=n=N+1 is LAST c. The same literal index gives
CM=(c,x,0,3,-3), not M5. CM's identical physical shift 3h is below its
actual top length b because b-3h=1-2h>0. It has RF(2,0)->V=(y,x,0,-1,2),
with shift 1-h in (0,1), then the existing V->W->T->C suffix. CM's exit
has four edges, and T2's t=0 exit has five.

The c-prefix in CM is (0,1,1); M5's y-prefix is (1,0,1). Their RF(2,0)
children are V and F0 respectively, despite equal source offsets and shifts.
Both are true typed interior edges. The canonical certificate uses the
constant t=0 face and shifted t>=1 cone, preserving this endpoint distinction.
M5, CM and F0 receive selected exits only; no complete stars are registered.
T2's inherited star remains bound to its original certificate.

## Genuine two-cycle and two nonclosure statements

The uniform cycle

    T(0,1)->Y4(d+1,0)->T

uses actual strictly intersecting occurrences, including n=3, and survives
under reversal. Both states have typed exits. In particular a strict rank
decrease on every edge would require rank(T)>rank(Y4)>rank(T), so the
all-child result is not an all-edge descent certificate.

Y4 belongs to S41, while D5 and its reversal do not. The actual LL(A+1,n)
edge uniformly escapes S41. The eighteen-label outgoing image is also not
forward closed: T belongs to it but T(0,1)->Y4 leaves it; independently,
R5(t+1,1)->R(B2h) has c-coordinate -2 outside that image's +/-1 values.
All these productive exits and cycles coexist. No closed obstruction is inferred.

## Separate complete-star and uniform-exit inventories

S41 remains P3's 37-label image plus X/R(X) and D3/R(D3). Every row has
separate before/after star and exit interfaces.

| S41 inventory | Before Y4 | After Y4 |
| --- | --- | --- |
| Registered nonterminal complete stars | 26 | 28 |
| Terminal C | 1 | 1 |
| Unregistered complete-star labels | 14 | 12 |
| Registered uniform exits, including C | 27 | 31 |

Y4's two orientations gain complete stars, retaining their already registered
exits. T2's orientations gain uniform exits, retaining their existing stars.
R5's orientations belong to S41 and gain exits without complete-star coverage.
D5, M5, CM and F0 do not inflate its count. Thus all 29 registered star/terminal
labels now have registered exits, while R5 contributes the two additional
labels with exits but unclassified stars. Ten S41 labels lack registered exits.

In the Y4 image, fourteen of eighteen labels have registered complete stars,
and all eighteen have registered exits. R5 and D5 orientations account for
the four star gaps. This does not classify their descendants. The older
R3/D3 36-label image now has 22 registered stars and 22 registered exits;
fourteen of those 36 labels still lack registered exits. Registries record
named interfaces, not a claim that every other repository method is inapplicable.

## Evidence, negative controls and replay

Canonical module kernel/psc/class_a_boundary_y4_children.mojo, with native
driver/regression and dedicated .github/workflows/class-a-boundary-y4.yml.
Native k=0..7,t=0..6 replay: 56 members, 112 complete-star cells,
784 selected-path source cells, 33,096 literal pairs, 2,352 accepted
occurrences, 3,104 selected source-path edges and 13,536 all-child walk edges.
Every accepted indexed first choice has its entire produced walk verified;
maximum walk length eight is attained. Both orientations and all eighteen
image labels are checked.

Independent literal-word/integer-polynomial/Fraction replay at k=0..12,t=0..8:
117 members, 234 complete-star cells, 1,638 selected-path source cells,
122,616 pairs, 6,552 accepted occurrences, 6,500 selected source-path edges
and 39,676 all-child walk edges. It independently reconstructs every literal
prefix and every reversed accepted child. The 512-refinement exact sign budget
refuses on exhaustion. Finite grids validate implementation; the exact guard,
index-cone and complete uniform tail arguments above supply the quantifiers.

Controls preserve the n=3 LR event that replaces a fictitious RR strip,
T2's t=0 LAST c endpoint, the different M5/CM prefixes, R5's bottom y prefix,
and actual C's equal types. They reject corrupt field identities, bad inputs,
disjoint legal pairs, wrong interior image targets, omitted/duplicate/corrupt
native registry rows, incomplete/duplicate stars, truncated/altered all-child
walks, false unequal-type zero terminals, unknown tail dispatch targets and
unsupported companion complete-star requests.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_boundary_y4_children.mojo
pixi run --locked mojo run -I . class_a_boundary_y4_children.mojo
cd ..
python -m pytest -q tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python oracles/python/class_a_boundary_y4_children.py > /tmp/y4.json
cmp /tmp/y4.json evidence/class-a-boundary-y4-2026-10-28/probe.json
sha256sum -c evidence/class-a-boundary-y4-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-y4-2026-10-28/SHA256SUMS
bash tools/verify_all.sh provenance
```

The evidence README distinguishes completed local checks, formal-tool failures
and pending hosted acceptance. No full-suite success is inferred. Preserve
124 governed claims, 34 named Lean proofs and 325 source openings. Independent
human review remains pending.

## Next complete-star gap and remaining scope

R5=(x,y,1,-1,-1) is a uniform actual Y4 LAST/RUN (A+1,N) child, with
strict source shift zeta>0. Its uniform three-edge exit is now certified,
but its complete star is unclassified. D5 is another outgoing star gap despite
its direct C edge.

All-source cyclic strict-zipper coverage, plus chambers, target-aware BH,
non-unit internal-space/return-lattice realization, universal BH/#139,
A1-prime, G1 and PSC remain open. The new all-child quantifier applies only
to the two Y4 orientations. Complete new companion stars, all-T2-child
productivity, forward closure and all-edge descent are not concluded.
