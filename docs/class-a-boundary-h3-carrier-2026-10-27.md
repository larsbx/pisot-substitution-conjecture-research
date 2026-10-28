# Class-A minus boundary: H3's exact half-chamber and five-step exits

Status: eight oriented source families have complete actual child stars and
selected physical typed-coincidence exits of length at most five on the whole
minus chamber. Their outgoing union has 76 typed labels. This is not global
forward closure or universal BH. Independent human review pending.

## Work shown

### Assumptions and hypotheses

The [stop/go](class-a-boundary-h3-stopgo-2026-10-27.md) retains the existing
three-source literature review, all-source coverage and non-unit realization
firewalls. Continue k,t>=0, n=k+3+t, d=2n-1-k, A=n+d=2n+t+2, N=n-1.
The actual ordered images are x->x y^A x, c->c y^n x, y->x y^N c.
Keep all bottom-minus-top integer Parikh coordinates and ordered occurrences.

Use the dependency certificates h=1/beta, alpha=beta-(n+2), b=1+h,
u=d/(beta-1), a=b+u=2+alpha-h, and
0<h<1/2, 0<alpha<1, 1<u<2, v=alpha+h in (0,1),
w=alpha+2h in (0,1). The last upper bound is explicitly replayed through
certify_tm_children, not inferred merely from v<1. Its exact identity is
beta^2*(1-w)=beta*(beta-t-5)+2>0 using beta>n+2=t+k+5.
Strict physical overlap means -length_bottom < shift < length_top.

The base source labels are
H3=(x,y,0,-1,3), J=(y,x,1,2,-4), K=(y,x,-1,-2,5),
L=(y,x,0,3,-4), plus each actual orientation reversal R(p,q,z)=(q,p,-z).
K here names a packet, not a manuscript theorem. The normalized shifts of
H3,J,K,L are 2-h,v,1-v,-1+3h. All are strictly interior. Their inflated
shifts are 2beta-1, t+4-2h, k+1+w, 3-beta; full transports are:

| Source | M applied to full offset |
| --- | --- |
| H3 | (2,2,2n-3) |
| J | (0,-2,t+6) |
| K | (1,3,k-4) |
| L | (-1,-1,4-n) |

H3 is reached uniformly from E- of #357 at (0,n+3). No assertion that
all other relevant strict-zipper states are covered is made.

### Derivation / reduction

#### The strict alpha=1/2 separator

For the minus characteristic polynomial
f(X)=X^3-(n+2)X^2+(n-d-1)X+2, exact clearing gives

8f(n+5/2)=S(k,t)=4k^2+20k-4t^2-24t+5.

The other two roots lie in (-1,1), so at X=n+5/2>1 the sign of f(X)
is the sign of X-beta. Thus S<0 iff alpha>1/2. The entire nonnegative
integer chamber splits into these exact coefficient-positive cones:

* k=t+r+1, r>=0: S=4t(2r+1)+4r^2+28r+29>0.
* t=k+r+1, r>=0: -S=4k(2r+3)+4r^2+32r+23>0.
* k=t=r+2: -S=4r+3>0.
* (k,t)=(0,0),(1,1): S=5,1>0.

These are polynomial identities and positive coefficients, not fitted tests.
No boundary equality is possible (also S is 1 modulo 4). Consequently

alpha>1/2 iff t>k or (t=k>=2).

Write e=1 in this high chamber and e=0 otherwise. The two small diagonal
exceptions are essential; replacing the condition by t>=k is false.
The canonical kernel checks the cleared cubic identity, every shifted cone
and both exceptional constants. Finite sign controls separately compare
2alpha-1 in the independent Perron embedding.

#### Complete nine-kind tables

Every nonfirst proper prefix of sigma(x) or sigma(y) is (1,0,index-1),
with the appropriate last run length. The physical first/run/last starts
are 0,a+i-1,a+run length. Every run index is clipped to its actual word:
H3 top 1..A, bottom 1..N; J/K/L top 1..N, bottom 1..A.
Let delta=i-j. Empty run intervals contribute nothing.

| Kind | H3 | J | K | L |
| --- | --- | --- | --- | --- |
| first/first | none | none | k=0 | none |
| first/run | none | none | none | j=n-2..n |
| first/last | none | none | none | none |
| run/first | i=2n+2..min(A,2n+4+e) | i=t+2..min(N,t+4) | i=max(1,k)..k+2 | none |
| run/run | delta=2n+3+e,2n+4+e | delta=t+3,t+4 | delta=k+1,k+2 | delta=-n,1-n |
| run/last | none | none | none | none |
| last/first | t<=1 or (t=2,e=1) | k<=1 | none | none |
| last/run | j=max(1,t-1-e)..t+1 | j=max(1,k-1)..k | j=t+1,t+2 | j=2n-1,2n |
| last/last | none | none | none | none |

For a positive run/run delta, take
1<=j<=min(bottom_run,top_run-delta), i=j+delta.
For L take every i=1..N and j=i-delta; the largest j is 2n-1<=A.
The first or last ordinal in an endpoint row is the literal word endpoint:
0 or A+1 for H3 top; 0 or n for J/K/L top; likewise on the bottom.
For the four reversed sources, swap the actual (i,j) and negate the full
typed target. This preserves strict overlap after exchanging the two intervals
and translating, and follows algebraically by negating the affine prefix update.
It does not identify two packets or erase their orientations.

Here are the guard reductions and exclusions needed to reconstruct the table.

* H3: first pairs are disjoint since 2beta-1>a. Run/first requires
  2n+1+v<i<2beta; this gives 2n+2..2n+4+e before the word clip.
  Run/run requires abs(2beta-1+j-i)<1, giving the two listed deltas.
  Run/last shift is at least k+4+2alpha>1 and is disjoint.
  Last/first has shift v-t-1; its nontrivial margin is
  a+v-t-1=1+2alpha-t, giving the stated t and e condition.
  Last/run shift j-t+2alpha gives j>=t-1-e and j<=t+1;
  the upper margin uses 0<v<1. Last/last shift k+3+2alpha>a.
* J: run/first requires t+2-v<i<t+5-2h, giving t+2..t+4
  with the actual N clip. Run/run has B=t+4-2h in (t+3,t+4).
  Last/first requires B>N, equivalently 2-k-2h>0, hence k<=1;
  its other margin is automatic. Last/run bounds are
  k-2+2h<j<k+3h, giving k-1..k clipped to j>=1.
  All first pairs have B>a, and run/last and last/last exceed their
  upper tile lengths because d-n=t+2 and B>0.
* K: B-a=k-1+3h, so first/first occurs exactly at k=0 (3h<1).
  Run/first requires k-1+3h<i<k+2+w, hence k..k+2 clipped at one.
  Run/run has B in (k+1,k+2). Last/first fails since B-N=w-t-1<0.
  Last/run bounds t+1-w<j<t+3-v give exactly t+1,t+2.
  First/run and first/last require B<0, which fails; run/last and
  last/last are farther to the right than the top tile.
* L: B=3-beta. First/first has B+a=3-n-h<0. First/run bounds
  n-3+h<j<n+alpha give n-2..n. Run/first requires i<4-beta<0.
  Run/run has B in (-n,1-n), giving delta=-n,1-n.
  Last/first fails B>N. Last/run bounds 2n-2+alpha<j<2n+v
  give 2n-1,2n. First/last and run/last are disjoint since
  B+A=d+1-alpha>N; last/last shift t+4-alpha>b.

In the J and K bounds, 3h<1 follows from beta>n+2>=5. All endpoint
ranges are word-legal: A=2n+t+2, N=k+t+2 and d>=5. These bounds
also show that every scalar endpoint used by the member interface fits
inside its already checked A+2 range. The symbolic certificate checks the
full incidence identities at legal index basis 1,2 while k,t remain symbolic,
then checks each selected occurrence as a cone-legal prefix identity.

#### Exact outgoing union and multiplicities

The base target labels are obtained by substituting the table into the full
Parikh prefix formula:

| Source | Types | (x,c) | y |
| --- | --- | --- | --- |
| H3 | y/x | (1,2) | -7..-4 |
| H3 | y/y | (2,2) | -8..-6 |
| H3 | x/x | (1,2) | -7..-5 |
| H3 | x/y | (2,2) | -8..-5 |
| J | y/x | (-1,-2) | 3..5 |
| J | y/y | (0,-2) | 2,3 |
| J | c/x | (-1,-2) | 3,4 |
| J | c/y | (0,-2) | 2,3 |
| K | x/x | (1,3) | -4 |
| K | y/x | (0,3) | -5..-3 |
| K | y/y | (1,3) | -6,-5 |
| K | c/y | (1,3) | -6,-5 |
| L | x/y | (0,-1) | 1..3 |
| L | y/y | (-1,-1) | 3,4 |
| L | c/y | (-1,-1) | 3,4 |

There are 38 distinct base labels. Their reversals are distinct from the base
union, giving exactly 76 across the entire chamber. Containment follows from
parameter cancellation and the full index clips, not from a sampled union.
Actual exact finite witnesses attain each label, proving attainment of the
finite envelope. Not every member attains all 76, and this union is not
forward closed. In particular its one-step image contains no zero-offset
terminal; the selected exits use the separately certified H1 family.

Ordered child counts per oriented source are 2t+3 for H3, 2k+2 for J,
2t+6 for K, 2n+3 for L. For H3, the terms are
2min(t+1,3+e)+max(t-1-e,0)+max(t-2-e,0)+[t<=1 or (t=2,e=1)],
which sum to 2t+3 on every applicable case. The other counts follow by
summing the two diagonal strip lengths and bounded endpoint ranges.
Production synthesis is O(n+d), with scalar target membership and no Cartesian
occurrence loop. The native regression deliberately uses that Cartesian loop
as an independent control of completeness.

### Selected exits and scoped descent

The base H3 path is uniform throughout k,t>=0:

| Source | Actual (i,j) | Typed target |
| --- | --- | --- |
| H3 | (2n+2,0) | J |
| J | (t+2,0) | K |
| K | (k+1,0) | L |
| L | (0,n-2) | H1=(x,y,0,-1,1) |
| H1 | (1,2) | C=(y,y,0,0,0) |

The table proves the first four strict overlaps; the last is the already
certified H1 typed coincidence. Word bounds are A-(2n+2)=t,
N-(t+2)=k, N-(k+1)=t+1, n-2>=1 and N>=2. The full Parikh targets
are polynomial identities, not merely shifts. J,K,L use the respective path
suffixes. Each reversal swaps the same actual indices and reverses every
intermediate typed packet; C is fixed. Thus the eight sources reach typed
coincidence in 5,4,3,2 steps according to their family.

Assign ranks 5,4,3,2,1,0 to H3,J,K,L,H1,C and the same ranks to their
reversed packets. The rank is defined only on these eleven distinct labels.
Every selected edge decreases it, and every submitted intermediate is checked.
All alternative geometric children remain in the complete star. L also has
an H3 child at (0,n), giving H3->J->K->L->H3; its H1 exit proves
that cycle is not a closed obstruction. No rank decreasing on all edges is
claimed, and no all-source rank is obtained by this finite packet assignment.

### Evidence and replay

Canonical kernel kernel/psc/class_a_boundary_h3_children.mojo; driver
kernel/class_a_boundary_h3_children.mojo. Local locked Mojo 1.1.0.dev2026090805
passed the complete native test: 56 members / 132,384 ordered pairs /
5,824 accepted / 1,568 selected path edges. It attains all 76 labels, verifies
all reversed edges, checks every actual pair against full Parikh and exact
Perron geometry, and independently separates high/low alpha with normalized
shifts 2alpha-2 and 2alpha. No floating arithmetic is used.

The separate literal-prefix integer-polynomial/Fraction oracle checks
117 members / 936 source cells / 490,464 pairs / 15,912 accepted /
3,276 selected path edges. It tests the separator by the exact algebraic sign
of 2beta-2n-5, not by a rounded root, and preserves actual witnesses for
all 76 labels. Its fixed sign-refinement budget refuses instead of guessing.
These finite controls validate the implementation; the universally quantified
proof is the cone/table derivation above.

From root:
```sh
python -m pytest -q tests/test_class_a_boundary_h3_children.py
python oracles/python/class_a_boundary_h3_children.py
python tools/make_proof_bank.py --check
bash tools/verify_all.sh provenance
```
From kernel/:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_h3_children.mojo
pixi run --locked mojo run -I . class_a_boundary_h3_children.mojo
```
Dedicated native/Python workflow: .github/workflows/class-a-boundary-h3.yml.
Receipts are in evidence/class-a-boundary-h3-2026-10-27/. No Lean/TLA source,
proof-bank inventory or governed theorem status changes. The inherited
conditional Lean lemmas do not formally prove this new table, and pending
hosted formal gates are retained as validation debt. Integration requires
fresh relevant acceptance receipts at the actual head.

### Negative controls

Reject the naive high rule t>=k at (0,0),(1,1), and the naive strict t>k
rule on the diagonal k=t>=2. Corrupting the cleared separator identity fails.
A low-chamber extra H3 run/first ordinal (2n+5,0) is rejected even when
word-legal, as is replacing the true high-diagonal last/first with its low
predicate. Actual word clips and empty strips remain part of every guard.

Invalid packet/ordinal, duplicate synthesis, envelope escape, out-of-packet
rank assignment and a corrupted intermediate with the correct final C all
refuse. A zero-offset unequal-type terminal fails the stronger typed-C
predicate, while genuine unequal-type offset-zero edges retain their own
geometric/BH meaning. Reversal keeps full offsets and actual swapped indices;
it cannot silently identify distinct target packets.

### Non-claims / remaining gaps

H3 and its three intermediates, with reversals, now have uniform physical
coincidence exits on the minus chamber. The complete 76-label image has not
been proved forward closed, nor has every cyclic seed-reachable strict-zipper
state been assigned a productive occurrence-compatible path. Plus-chamber
coverage and internal-space/return-lattice realization remain outside scope.
A next single unclassified packet is P=(y,y,-1,-1,3), reached uniformly
from L at (1,n), with normalized shift -alpha. Its complete outgoing star
and those of other image targets remain further closure obligations.
Universal BH/#139, A1-prime, G1 and PSC retain their existing open statuses.
