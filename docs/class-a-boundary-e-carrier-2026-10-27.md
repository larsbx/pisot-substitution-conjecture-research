# Class-A minus boundary: complete oriented E/H stars and short exits

Status: exact six-packet child classification and physical typed-coincidence
reachability. At most two selected steps suffice from each packet throughout
the minus chamber. This is not universal BH, all-source coverage or global
forward closure. Independent human review pending.

## Work shown

### Assumptions and hypotheses

Read the [continuation stop/go](class-a-boundary-e-stopgo-2026-10-27.md).
This reuses the same standard affine update and three-primary-source review
as #355; there is no new spectral or internal-space transfer. Work throughout
k,t>=0, n=k+3+t, d=2n-1-k, A=n+d, N=n-1, with actual words
x->x y^A x, c->c y^n x, y->x y^N c.
Keep the full bottom-minus-top Parikh triple and the actual ordered occurrence
indices. Let h=1/beta, alpha=beta-(n+2), b=1+h, a=b+u and u=d/(beta-1).
Previously checked polynomial/root certificates give

0<h<1/2, 0<alpha<1, 1<u<2, beta-a=n+h,
a=2+alpha-h, and 0<alpha+h<1.

The last bound is not numerical: the existing exact identity
beta^2*(1-alpha-h)=beta*(beta-t-4)+2>0 follows from
beta>n+2=t+k+5. Its remainder and coefficient margin are replayed through
the dependency certificate. Strict physical overlap is -length_bottom < shift
< length_top. Machine interfaces refuse overflow; the written proof and
polynomial certificate quantify over unbounded k,t.

Write R(p,q,w)=(q,p,-w), swapping the two actual occurrences as well.
The six source labels are E+=(x,x,0,0,1), E-=R(E+),
H1=(x,y,0,-1,1), R(H1), H2=(x,y,0,-1,2), R(H2).
Their shifts are respectively 1,-1,-h,h,1-h,h-1, so all have strict
interior overlap. In particular E- is #355's unresolved E packet.
R is used to construct distinct oriented packets, not to identify or discard
one of their targets.

### Derivation / reduction

The base sources E+, H1, H2 have inflated shifts beta, -1, beta-1,
and full incidence transports (1,1,N), (0,0,-1), (1,1,n-2).
For their proper prefixes, every nonfirst prefix has x-coordinate one and
c-coordinate zero: a run ordinal i has prefix (1,0,i-1), a last ordinal
has (1,0,run length). Their physical first/run/last starts are
0,a+i-1,a+run length. Thus the following table exhausts every child kind.
All run indices obey top 1..A; bottom 1..A for E+ or 1..N for H1/H2.

| Top / bottom kind | E+ | H1 | H2 |
| --- | --- | --- | --- |
| first/first | none | (0,0) | none |
| first/run | none | (0,1) | none |
| first/last | none | none | none |
| run/first | i=n+1..n+3,j=0 | none | i=n..n+2,j=0 |
| run/run | i-j=n+2,n+3 | j=i+1, i=1..n-2 | i-j=n+1,n+2, j=1..N |
| run/last | none | i=N,N+1,j=n | i=2n+1,2n+2,j=n |
| last/first | none | none | none |
| last/run | i=A+1,j=d-2..d | none | none |
| last/last | none | none | none |

For E+ run/run delta=i-j, the exact free range is 1<=j<=A-delta.
Both ranges are nonempty because d>=5. For every odd orientation reverse
the ordered indices and apply R to the full typed target. This gives all
nine kinds of all six sources, including last/run versus run/last.

Here are the full inequality reductions behind every row and exclusion.

* E+ run/first shift is beta-a-i+1=n+1+h-i. Its guard is
  n+h<i<beta+1, giving exactly n+1..n+3. Run/run requires
  abs(beta+j-i)<1, giving i-j=n+2,n+3 from 0<alpha<1.
  Last/run shift is 1+alpha+j-d; its bounds give
  d-2-alpha<j<d+1-h, exactly d-2..d. All first pairs and last/last
  are disjoint because beta>a. Run/last shift is at least beta+1>1.
  Last/first has shift h-d, whose lower margin a+h-d=2+alpha-d<0.
* H1 first/first has shift -1, inside (-a,a). First/run shift is
  a+j-2, so only j=1 intersects; j=2 is exact endpoint contact.
  Run/first shift -a-i is disjoint. Run/run shift j-i-1 is an integer
  and lies in (-1,1) only at zero, giving j=i+1 and typed y/y coincidence.
  Run/last shift N-i must be an integer in (-b,1), exactly -1 or 0;
  these give i=N+1,N. Last/first is below -a, last/run is below -1,
  and last/last shift -d-2 is below -b. First/last is beyond top length.
* H2 has beta-1>a, so every first pair is disjoint. Run/first shift
  beta-a-i=n+h-i gives n-1+h<i<beta, hence i=n..n+2.
  Run/run requires abs(beta-1+j-i)<1, so i-j=n+1,n+2;
  every j=1..N is actual since its largest i is 2n+1<=A.
  Run/last shift is 2n+1+alpha-i. The exact bounds are
  2n+alpha<i<2n+2+alpha+h, giving i=2n+1,2n+2.
  Both are word-legal even on t=0, because A-(2n+2)=t>=0.
  Last/first has lower margin 1+alpha-d<0. Last/run requires j>=d-1,
  exceeding N since d-n=t+2. Last/last shift alpha-t-2 has lower
  margin alpha+h-t-1<0. The strict bound alpha+h<1 is essential here.

The full Parikh update is affine in each free run index. The canonical
polynomial certificate checks its legal index basis 1,2 while n,d remain
symbolic in Q[t,k], checks every first/last combination for all six oriented
sources, and checks the selected path occurrences with cone-legal bounds.
No geometrically disjoint child is accepted merely because its word exists.

Orientation reversal follows directly: exchanging the two prefixes negates
M*w+prefix_bottom-prefix_top, and exchanging the two intervals then translating
by the negative shift preserves strict interior overlap. Hence an edge at
(i,j) becomes exactly the edge at (j,i) to R(target). The native regression
also verifies this with the independent generic actual-word/Perron kernel.

### Exact target packet and multiplicities

The base-source target sets are parameter-free:

| Base source | Child types | (x,c) | y |
| --- | --- | --- | --- |
| E+ | y/x | (0,1) | -3,-2,-1 |
| E+ | y/y | (1,1) | -4,-3 |
| E+ | x/y | (1,1) | -4,-3,-2 |
| H1 | x/x | (0,0) | -1 |
| H1 | x/y | (1,0) | -1 |
| H1 | y/y | (0,0) | 0 |
| H1 | y/c | (0,0) | -1,0 |
| H2 | y/x | (0,1) | -3,-2,-1 |
| H2 | y/y | (1,1) | -4,-3 |
| H2 | y/c | (1,1) | -4,-3 |

The base union has 15 labels. Add every orientation reversal: only the typed
coincidence C=(y,y,0,0,0) is fixed, so there are exactly 29 distinct labels.
Substitution of the index ranges proves containment. Every row is attained
in every member: d-3>=2, n-2>=1, and all fixed endpoint ranges are actual.
Thus 29 is the exact image for each member, not just a finite sampled union.
The independent receipt preserves concrete witnesses as an additional check.

The ordered child counts per source are 2d+1 for E+ and E-, n+2 for H1
and R(H1), and 2n+3 for H2 and R(H2). Multiplicities are retained until
projection to typed labels. Production synthesis traverses at most two diagonal
run/run strips and bounded endpoint ranges, in O(n+d) time and output space.
The target predicate uses fixed scalar tests, not a rebuilt list in the loop.

### Uniform short typed-coincidence exits

C=(y,y,0,0,0) is an actual equal-type zero-offset terminal. The selected
paths and their actual occurrences are:

| Source | First occurrence and target | Final occurrence to C |
| --- | --- | --- |
| E+ | (n+1,0) -> R(H1) | (2,1) |
| E- | (0,n+1) -> H1 | (1,2) |
| H1 | (1,2) -> C | already terminal |
| R(H1) | (2,1) -> C | already terminal |
| H2 | (n,0) -> R(H1) | (2,1) |
| R(H2) | (0,n) -> H1 | (1,2) |

The tables prove all word bounds, full typed transport and strict geometry.
For example E+'s (n+1,0) target is (y,x,0,1,-1)=R(H1), while H2's
(n,0) target is exactly the same packet. H1's (1,2) target has full offset
(0,0,-1)+(1,0,1)-(1,0,0)=0, and both children are y. Every reversed
path swaps the same real occurrence indices; no new realization is inferred.

Assign rank two to E+/E-/H2/R(H2), one to H1/R(H1), and zero to C.
Each selected edge strictly decreases this natural-number rank. The rank
refuses every other state, including a different equal-type zero-offset
terminal; this fixes the exact intended packet. It is not a rank on all edges.
In fact H1 also has a first/first child E-, giving the cycle E- -> H1 -> E-.
Its other run/run child exits to C. The cycle is therefore not a closed
obstruction, and no global all-edge descent is asserted.

### Evidence and replay

Canonical kernel: kernel/psc/class_a_boundary_e_children.mojo; driver:
kernel/class_a_boundary_e_children.mojo. The native test independently exhausts
all occurrence pairs, compares the table and synthesized star to full Parikh
transport plus exact Perron-field geometry, rejects duplicates, verifies the
actual reversed edge, and attains all 29 labels in every member.
Local locked native replay passed 56 members / 148,288 pairs / 7,112 accepted,
with 560 selected path edges. Its archived output pins the exact source bytes.

The independent literal-prefix integer-polynomial/Fraction oracle checks
117 members / 702 source cells / 542,880 ordered pairs / 19,422 accepted,
with 1,170 selected path edges and actual witnesses for all targets.
The fixed 512-refinement sign budget refuses instead of guessing.
The uniform mathematical statements are proved by the inequalities above;
these exhaustive finite controls validate the implementation separately.

From root:
```sh
python -m pytest -q tests/test_class_a_boundary_e_children.py
python oracles/python/class_a_boundary_e_children.py
python tools/make_proof_bank.py --check
bash tools/verify_all.sh provenance
```
From kernel/:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_e_children.mojo
pixi run --locked mojo run -I . class_a_boundary_e_children.mojo
```
Dedicated native/Python workflow: .github/workflows/class-a-boundary-e.yml.
Receipts and SHA256SUMS: evidence/class-a-boundary-e-2026-10-27/.
No Lean/TLA source or governed theorem status changes. The 34 named-proof
inventory is inherited, and fresh applicable hosted checks remain required.
The #355 formal-gate queue is recorded as validation debt, not credited from
its merge status. Local Lean still fails before compilation; no new Lean
proof pass is asserted for these tables.

### Negative controls

Unavailable ordinals and packet kinds, duplicate synthesis, corrupted full
symbolic transport, an intermediate edge altered while leaving the final C
unchanged, an unequal-type zero-offset terminal, and an out-of-packet rank
all refuse. H1's (0,2) first/run child is endpoint-only and has no interior
intersection. H2's extra (2n+3,n) child is disjoint even when that ordinal
is word-legal; on the t=0 face it is the last x rather than a run y.
The overly wide interval that ignores alpha+h<1 is explicitly countered.

H1's (N,n) child (y,c,0,0,0) is a genuine geometric zero-offset edge and
is retained by the complete carrier. It fails only the stronger equal-type
coincidence predicate, not the actual-overlap test. BH may accept offset-zero
or half-coincidence targets at its own scope; this distinction is preserved.

### Non-claims / remaining gaps

These six sources now have uniform bounded physical coincidence exits on the
minus chamber, including #355's formerly unresolved E-. The full 29-label
outgoing image is not proved forward closed. The next single unclassified
packet is H3=(x,y,0,-1,3), reached from E- at (0,n+3); its normalized shift
is 2-h, and that occurrence is word-legal throughout d>=5. The other target
packets, plus-chamber states, and every cyclic seed-reachable strict-zipper
state still require the coverage/target compatibility demanded by #139.
No all-source BH, return-lattice/internal-space realization, A1-prime, G1 or
PSC theorem follows. Existing theorem-status distinctions remain unchanged.
