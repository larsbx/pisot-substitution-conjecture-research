# A finite integer carrier and exact measure equations for paired overlaps

**Status:** written scoped proofs; independent human mathematical review
pending. The finite implementation and its replay are separate evidence.
No general C4, G1, BH, A1', pure discrete spectrum or PSC status is promoted.
The [targeted literature gate](c4-finite-overlap-carrier-literature-gate-2026-11-05.md)
precedes the new implementation.

## 1. Baseline, purpose and hypotheses

The initial inspected main revision was
`60536272b3d68b4f53ce772e7674efabce840fde`, containing merged #493, #494
and #495. The publication base is `cd575e2b` (subsequent merge of #483);
that change is independent of the present machinery. The lifted sets, Haar normalization and strict-cut lower bound
come from the mainline
[compact M-adic bridge](c4-nonunit-madic-counting-bridge-2026-11-04.md).
The existing
[finite-cylinder verifier](c4-finite-cylinder-overlap-verifier-2026-11-04.md)
already authenticates complete slices and conservative Euclidean enclosures.

Open [PR #496](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/496)
at inspected head `1da1da776fb0f23396eeb9c40e193ace3e0ada46` has a complete
paired-occurrence graph certificate for all 18 word orders of
`M=[[0,1,2],[1,1,1],[0,1,0]]`. Its common-attractor route is canonical;
the period-aware route remains an earlier variant. Those files and results
were on that PR branch, not this inspected main revision. The present
target is complementary: prove an a priori finite carrier, strengthen the
measure relation to an equality, and change the incidence in the finite
specialization. Repeating the completed 18-source class is not new coverage.

Let `sigma` be a primitive irreducible Pisot substitution on three letters,
with nonsingular column-incidence matrix `M`, Perron root `beta>1`, and
positive left length vector `ell`, so `ell M=beta ell`. Let
`W:R^3 -> R^2` be a real linear chart whose kernel is the Perron line.
Write `W M=B W`; the eigenvalues of `B` have modulus less than one.
The linear map

```text
Phi x = (ell x, W x)
```

is invertible. Put `D=abs(det M)`,
`H_M=inverse_limit_q Z^3/M^q Z^3`, and
`x_star=(W x,iota(x))`. The compact-factor Haar measure has total mass one.
On `E_hat=R^2 x H_M` use product measure `mu`. Let `T_M` be multiplication
by `M` on `H_M`, and put `A(u,h)=(Bu,T_M h)`, so
`A(x_star)=(Mx)_star`. The mainline bridge proves that `A` is
injective and scales `mu` by `beta^-1`.

For an actual one-sided fixed word of a power of `sigma`, let `K_c` be
the compact positive-prefix sets in this space. They have positive finite
measure. Assume a certified common Euclidean enclosure

```text
projection(K_c) subset Q=[-R_1,R_1] x [-R_2,R_2] for every c,
```

with positive rational radii. The proofs below use complete literal prefix
occurrences. They do not replace those occurrences by incidence counts,
selected paths, sampled prefixes or an unverified geometric model.

## 2. Authenticate the set equation at the chosen graph step

**Lemma F0 (common compact attractor).** The actual compact prefix sets
satisfy the complete one-step prefix-set equation, and therefore its
`q`-step version for every positive integer `q`. They are independent of
the chosen one-sided periodic fixed word.

*Proof.* Let `F` be the operator on triples of nonempty compact sets
whose `c`-th component is

```text
F(L)_c = union_{sigma(d)=P c S} (A L_d + p(P)_star).
```

Every component is nonempty, since primitivity implies that each letter
occurs in at least one image. Composition of prefix maps, keeping all
occurrences, gives the analogous formula for `F^n` and `sigma^n`.
If the selected word has period `k`, its literal decomposition gives
`K=F^k(K)`, as in the mainline bridge.

Give `H_M` its complete ultrametric in which agreement through residue
depth `r` has diameter at most `2^-r`. Multiplication by `M^m` has
Lipschitz constant at most `2^-m`; when `D=1` the compact factor is a
one-point space. Choose `m` divisible by `k` and sufficiently large that
`||B^m||<1` in a fixed Euclidean norm. The product metric and the maximum
Hausdorff metric on compact triples make `F^m` a strict contraction on a
complete space. Thus it has a unique fixed triple. The given `K` is one
such triple, and `F(K)` is another because powers of `F` commute.
Consequently `F(K)=K`. For two periodic fixed words, choose `m` divisible
by both periods; the same uniqueness argument identifies their triples.
This proves the assertion. No strong-coincidence witness is used.

For the remainder fix any positive integer `q`. We have

```text
K_c = union_{sigma^q(d)=P c S} (A^q K_d + p(P)_star).       (1)
```

The different occurrence pieces in (1) are measure-disjoint for each fixed
`c`. Indeed, the mainline positive-volume and Perron argument applies to
this equation: with `s_c=mu(K_c)`, subadditivity gives
`beta^q s <= M^q s`; pairing with the positive left vector `ell` forces
equality coordinate by coordinate. A finite union has the sum of its
piece measures only when distinct pieces have null intersections. This is
within-letter occurrence disjointness; no cross-letter disjointness is
assumed.

## 3. The physical strip is preserved by every actual paired occurrence

Define the translated pair intersection

```text
E(c,c',z) = K_c intersection (K_c' + z_star),    z in Z^3.
```

For occurrences `sigma^q(d)=P c S` and `sigma^q(d')=P' c' S'`, put
`p=p(P)`, `p'=p(P')`. If `z+p'-p` lies in `M^q Z^3`, the child offset is

```text
z_new = M^-q (z+p'-p),                                    (2)
```

and the paired intersection of the two occurrence pieces is exactly
`A^q E(d,d',z_new)+p_star`. If that integer-lattice membership fails,
their depth-`q` compact residue cylinders are disjoint. This exclusion is
exact quotient membership, not coordinatewise reduction modulo `D^q`.

If the child is normalized by track swapping, its literal translation
changes as well: `E(d',d,-z_new)=E(d,d',z_new)-z_new_star`, so the same
paired piece becomes
`A^q E(d',d,-z_new)+(z+p')_star`. Keeping only scalar target measures is
permitted because the two overlaps are translates of one another. A
literal normalized set equation must retain the adjusted translation.

**Lemma F1 (typed physical strip).** Every state `(c,c',z)` generated by
complete paired-prefix ancestry from a zero-offset root satisfies

```text
-ell_c < ell z < ell_c'.                                  (3)
```

*Proof.* At a zero-offset root the strict inequalities follow from positive
letter lengths. A proper prefix before `c` has physical length

```text
0 <= ell p <= beta^q ell_d - ell_c,
0 <= ell p' <= beta^q ell_d' - ell_c'.
```

Substitution into (2) gives

```text
-beta^q ell_d < ell z + ell p' - ell p < beta^q ell_d'.
```

Divide by `beta^q` to obtain (3) for the child labels `d,d'`.
Induction proves the claim. Normalizing a state by the track swap
`(c,c',z) -> (c',c,-z)` preserves the same typed strip.

This is a statement about every generated path, whether or not its overlap
is nonempty. In particular, with `H=max_c ell_c`, every generated offset
satisfies `abs(ell z)<H`. It is stronger than a geometric-series height
bound that treats the successive digits as unrelated.

## 4. A proved finite carrier replaces arbitrary offset truncation

**Theorem F2 (finite integer carrier).** Supply rational numbers
`L_ji >= abs((Phi^-1)_ji)` and `H_upper>=H`. Define

```text
C_j = L_j0 H_upper + 2 L_j1 R_1 + 2 L_j2 R_2,
N_j = floor(C_j),                 j=0,1,2.                 (4)
```

Every generated state with nonempty overlap has integer offset satisfying
`abs(z_j)<=N_j`. Consequently all possibly nonempty generated states lie
in the finite carrier

```text
{0,1,2}^2 x product_j {-N_j,...,N_j},
```

whose cardinality is at most `9 product_j(2N_j+1)` before track-swap
normalization.

*Proof.* If `E(c,c',z)` is nonempty, subtracting the two Euclidean
coordinates gives `Wz in Q-Q`. Thus `abs((Wz)_i)<=2R_i`. Lemma F1 gives
`abs(ell z)<H`. Apply `Phi^-1` and the triangle inequality to obtain
`abs(z_j)<=C_j`. Since `z_j` is integral, (4) follows.

An offset outside this **proved** carrier may be discarded as an empty
child intersection. Starting at the selected zero-offset roots and
processing every retained state once therefore yields a finite closed
graph: only finitely many carrier states can be discovered, and each has
finitely many actual paired occurrences. The displayed count supplies
an a priori closure bound. No bound on a balanced-pair system's number of
states or phase period enters the proof.

The distinction from a resource cap matters. An unproved smaller offset
cutoff or an exhausted state/iteration budget still means inconclusive.
Theorem F2 permits geometric exclusion only after the chart, radii,
inverse bounds and source ancestry have been authenticated. A certificate
must start from its declared roots and reconstruct complete reachable rows;
an arbitrary serialized graph is not admitted by having small offsets.

Optional interval pruning may discard a child when it proves `Wz` lies
strictly outside `Q-Q`. Boundary contact or uncertainty is retained.
Merely retaining an uncertain interval does not prove that its true `Wz`
is inside `Q-Q`. This causes no problem: the proved integer carrier can
still be applied, because its exclusion proof concerns nonempty overlaps.

This is a uniform construction from the supplied substitution and
enclosure data. It is not one numerical bound for all Pisot substitutions,
a polynomial-time complexity claim, or finiteness of the balanced-pair
algorithm itself.

## 5. Complete occurrence graphs give an exact measure equation

Build the finite graph as above. Every actual paired occurrence contributes
one edge unless its intersection has been proved empty. In particular,
multiple occurrences with the same target remain multiple edges. Let
`T_ij` count these edges from state `i` to state `j`, and put
`v_i=mu(E_i)`.

**Theorem F3 (exact paired-overlap measure relation).**

```text
v = beta^-q T v,           0 <= v_i <= area(Q).             (5)
```

*Proof.* Intersect the two complete unions in (1), one of them translated
by `z_star`. This is the union indexed by all pairs of occurrences.
Two different paired pieces have null intersection: if their first
occurrences differ, their intersection lies in a null intersection of
two occurrence pieces of `K_c`; if the first occurrences agree but the
second differ, use the corresponding null intersection in the translated
`K_c'`. Thus the finite paired union is measure-disjoint.

Nonintegral children and the other certified exclusions are empty.
Each retained child is an affine `A^q`-image of its target overlap, so
its measure is `beta^-q v_j`. Track swapping replaces an overlap by a
translate and preserves its measure. Summing all retained occurrences,
including repeated targets, proves (5). Finally `E_i` is a subset of one
lifted tile, whose Euclidean projection is contained in `Q` and whose
compact factor has Haar measure at most one.

The usual subcritical certificate remains valid: if a strictly positive
vector `w` satisfies `T w <= lambda w` for `lambda<beta^q`, then the
maximum of `v_i/w_i` and (5) force `v=0`. For positive integer weights,
iteration also gives the explicit upper bound

```text
v_i <= area(Q) w_i (lambda/beta^q)^n.
```

The equality is stronger than the subadditivity relation alone. Its proof
requires the within-letter occurrence-disjointness established in Section
2; an arbitrary family of overlapping outer rectangles would supply only
an inequality and does not inherit (5).

## 6. Positive overlap requires a reachable critical component

**Corollary F4 (necessary critical SCC).** If a root overlap has positive
measure, it reaches a strongly connected component `S` of the complete
graph whose nonnegative adjacency matrix satisfies

```text
rho(T_S) = beta^q.                                        (6)
```

*Proof.* Equation (5) implies that a zero-measure state has no edge to a
positive-measure state. Hence every SCC that contains one positive-measure
state consists entirely of positive-measure states. Within the subgraph
of positive-measure states reachable from the root, choose a sink SCC
`S`. Every outgoing edge from `S` to a state outside `S` has zero target
measure. Restricting (5) therefore gives
`T_S v_S=beta^q v_S`, with every entry of `v_S` strictly positive.
Perron--Frobenius yields (6).

Consequently, proving that no reachable SCC is critical proves the root
overlap null. Both subcritical and supercritical SCCs can occur in this
criterion. A supercritical SCC alone cannot support a positive solution
on a sink of the positive-measure support.

Criticality is necessary, not sufficient. The zero vector also solves
the homogeneous system, and an algebraic eigenvector does not establish
the geometric realization or positivity of actual overlap measures.
Finiteness by itself is insufficient as well: a diagonal root
`E(c,c,0)=K_c` has positive measure under the same standing Pisot
hypotheses. It cannot admit a strict subcritical certificate.

If all three unshifted distinct-letter roots are certified null for a
source, Theorem M1 of the mainline bridge excludes every nonempty finite
fully strict child-closed noncoincident balanced-pair set for that source:
its represented cut-pair overlaps would form a null union, whereas the
strict-cut theorem forces measure at least `kappa/L_max>0`. This does not
extract such a finite component from an arbitrary failure.

### An algebraic exclusion corollary, separate from implementation

**Corollary F5 (polynomial obstruction).** Let `g` be the minimal
polynomial of `beta^q`. If the integer matrix `g(T)` is nonsingular, then
every overlap represented by the complete graph has measure zero.

Indeed, (5) implies `T v=beta^q v`, hence `g(T)v=0`. Nonsingularity
forces `v=0`. One sufficient exact certificate would be invertibility
of `g(T)` modulo a prime: its determinant is then nonzero as an integer.
Failure modulo one prime is inconclusive. This is an optional algebraic
route, not a claim that such modular certificates have been generated.

## 7. A different incidence: the twelve-source class containing `11/210/10`

The new finite source domain is

```text
sigma(0)=11,
sigma(1) in {012,021,102,120,201,210},
sigma(2) in {01,10}.
```

These are exactly twelve literal substitutions with incidence

```text
M=[[0,1,1],[2,1,1],[0,1,0]],
M^2=[[2,2,1],[2,4,3],[2,1,1]],
det M=2,
chi(x)=x^3-x^2-3x-2.
```

The square is positive. None of `-2,-1,1,2` is a root of the monic
cubic, so it is irreducible. Its discriminant is `-107`; it has one real
root `beta>2`, and the complex conjugates have squared modulus
`2/beta<1`. The rational isolation

```text
2.5115 < beta < 2.5116,
chi(2.5115)=-0.000513854125,
chi(2.5116)= 0.000576200896
```

uses exact terminating decimals, equivalently rational numbers.
This incidence differs from #496's completed class; its characteristic
polynomial already rules out obtaining it by relabelling that class.

Choose the normalization `ell_0=1`, and set

```text
a=(beta+1)/beta^2=(-beta^2+3 beta+1)/4,
b=1/beta=(beta^2-beta-3)/2,
gamma=b+1/2,
ell=(1,beta/2,gamma),
F=(beta+1,beta^2,beta),
W x=(x_0-a x_1,x_2-b x_1),
B=[[-2a,1-a],[-2b,-b]].
```

Exact polynomial reductions give `M F=beta F`, `ell M=beta ell`,
`W M=B W` and `a gamma=1/2`. The last identity follows directly from
`beta^3=(beta+1)(beta+2)`. All entries of `ell` are positive, and
`H=max ell_c=beta/2` in this normalization.

The covolume in the physical/chart coordinates is

```text
kappa=abs(det Phi)=a+beta/2+b gamma=3a+1/2
     =(5+9 beta-3 beta^2)/4 > 0.
```

For `h=ell x`, `u=(Wx)_0`, `v=(Wx)_1`, the inverse chart is explicit:

```text
x_1=(h-u-gamma v)/kappa,
x_0=(a h+(kappa-a)u-v/2)/kappa,
x_2=(b h-bu+(kappa-b gamma)v)/kappa.                       (7)
```

Thus certified rational coefficient bounds and a common Euclidean box
can be inserted directly into Theorem F2. The physical strip uses these
lengths; the Haar factor at depth `q` is `2^-q`. Neither normalization
may be changed silently when comparing a volume with a cut-density bound.

For a two-generation graph, the minimal polynomial of `theta=beta^2` is

```text
g(t)=t^3-7t^2+5t-4.
```

Indeed `beta=(theta+2)/(theta-3)`, so `Q(theta)=Q(beta)`, and substitution
gives the displayed cubic. Corollary F5 would therefore use
`T^3-7T^2+5T-4I`. This algebraic consequence does not claim an implemented
modular-matrix verifier.

## 8. Finite results and replay boundary

An independent exact oracle reconstruction has checked the common box
`Q=[-8,8]^2` for every source in the new twelve-source class. Its rational
block certificate is

```text
|B^12| <= [[313,103],[184,148]]/1000,
D=(41/10,24/5),
D+|B^12|(8,8) <= (7.428,7.456) < (8,8),
beta^2 > 63/10.
```

Here `D` bounds every proper-prefix digit in all three twelfth-level
images, with 178,973 digits per source. The displayed decimals are exact
rational numbers. The complete block equation and strict linear
contraction imply containment in `Q`, by the same compact-maximum
argument used in the mainline finite-cylinder verifier. These are
enclosure parameters checked by both the native prefix-hull recursion and
an independent literal enumeration. Neither method samples the digits.

### 8.1 Computed carrier and complete finite graphs

All six canonical letter-pair carriers have the same inclusive integer box

```text
z_0 in [-15,15], z_1 in [-14,14], z_2 in [-16,16].
```

Each typed box contains at most `31*29*33=29,667` offsets. The six-box
capacity is **178,002** before further same-letter sign normalization.
These are computed inverse-chart bounds, not chosen search cutoffs. The
actual state budget is 20,000 per source; reaching it would refuse a
conclusion. The complete graphs close well below it.

Every graph uses `q=2`, all three zero-offset distinct-letter roots, and
all literal paired occurrences. Every retained repeated edge is counted.
The exact common rate is `lambda=125/20=25/4<63/10<beta^2`.

| Index | Images `sigma(0)/sigma(1)/sigma(2)` | States | Edges | Weight sweeps | Maximum weight |
| ---: | --- | ---: | ---: | ---: | ---: |
| 0 | `11/012/01` | 3,664 | 21,151 | 51 | 3,070 |
| 1 | `11/012/10` | 3,649 | 21,164 | 123 | 4,553 |
| 2 | `11/021/01` | 3,667 | 21,103 | 41 | 2,418 |
| 3 | `11/021/10` | 3,667 | 21,033 | 520 | 15,778 |
| 4 | `11/102/01` | 3,653 | 21,186 | 47 | 2,936 |
| 5 | `11/102/10` | 3,667 | 21,168 | 50 | 1,872 |
| 6 | `11/120/01` | 3,693 | 21,144 | 467 | 15,995 |
| 7 | `11/120/10` | 3,674 | 21,203 | 47 | 2,434 |
| 8 | `11/201/01` | 3,643 | 20,976 | 52 | 1,887 |
| 9 | `11/201/10` | 3,643 | 21,054 | 41 | 2,893 |
| 10 | `11/210/01` | 3,646 | 21,095 | 117 | 4,595 |
| 11 | `11/210/10` | 3,649 | 21,118 | 67 | 3,087 |
| **Total** | **12 sources** | **43,915** | **253,395** | | |

The graphs reject 1,248,456 paired occurrences by exact nonintegrality and
162,503 by strict stable-box separation. After those checks there are zero
carrier rejections. That observed zero does not supply the carrier theorem;
the theorem and authenticated inverse-chart bounds independently establish
the finite ambient domain.

The final positive integer vectors satisfy, for every retained row,

```text
125*w_i - 20*sum_occurrence_edges(i,j) w_j >= 125.
```

The minimum gap in every source is exactly 125. The maximum weight over
the class is 15,995, below the explicit accepted budget of one million.
Consequently Theorem F3 proves `mu(K_c intersection K_d)=0` for all
**36 distinct-letter roots** in these twelve substitutions. This is a
finite source-domain conclusion from the written measure proof and the
exact finite certificates. No strong-coincidence witness is consumed.

Together with the mainline bridge's strict-cut lower bound (M1), these
null overlaps exclude every finite fully strict child-closed noncoincident
balanced-pair system for each source in this class, at M1's stated
hypotheses. This consequence has no additional bound on the number of
balanced-pair states or on their phase period. It does not assert that an
arbitrary failure of productivity supplies such a finite strict system.

### 8.2 A finite upper bound and the failed stronger rate

The same vectors give the explicit upper bound

```text
v_i <= 256*w_i*(125/126)^n.
```

For `n=3072` this is less than `1/10` even at the full permitted weight
budget. Both implementations check exact rational arithmetic. A short
independent verification is

```text
(126/125)^126 > 1+126/125+binom(126,2)/125^2+binom(126,3)/125^3
             = 41854/15625 > 8/3,
256*10^6*(3/8)^24 = 4412961507515625/288230376151711744 < 1/10,
3072 >= 24*126.
```

This finite bound and the limiting nullity conclusion are separate: the
latter uses the inequality for arbitrarily large `n`, justified by the
complete finite graph, rather than treating one small bound as zero.

The earlier, stronger proposed rate `124/20` succeeded on ten sources,
but indices 3 (`11/021/10`) and 6 (`11/120/01`) exhausted the one-million
weight budget. Those attempts are preserved as **inconclusive**, with
regressions that reproduce their refusal. The successful `125/20` rate
still has the required strict separation from `beta^2`.

### 8.3 Authentication, replay and scope

The canonical implementation is
[`c4_pair_overlap_carrier.mojo`](../kernel/psc/c4_pair_overlap_carrier.mojo)
and
[`c4_pair_overlap_new_incidence.mojo`](../kernel/psc/c4_pair_overlap_new_incidence.mojo).
The driver emits the complete ordered state/occurrence-row/weight packet.
The independent
[Python oracle](../oracles/python/c4_pair_overlap_new_incidence.py)
uses Fraction Gaussian elimination, exact cubic-field powers and literal
prefix enumeration. A second regression reconstruction uses cofactors,
rescanned prefix counts and rational interval pruning. The packet checker
compares every record, including metadata and repeated target indices.
The deterministic
[receipt](../evidence/c4-pair-overlap-new-incidence-2026-11-05/receipt.json)
records all counts and packet digests; process receipts and review scope
are in the
[evidence directory](../evidence/c4-pair-overlap-new-incidence-2026-11-05/README.md).

Replay from the repository root:

```bash
cd kernel
pixi run --locked mojo run -I . tests/test_c4_pair_overlap_new_incidence.mojo
pixi run --locked mojo run -I . c4_pair_overlap_new_incidence.mojo > /tmp/new-incidence-native.txt
cd ..
PSC_NEW_INCIDENCE_NATIVE_OUTPUT=/tmp/new-incidence-native.txt python -m pytest --assert=plain -q tests/test_c4_pair_overlap_new_incidence_oracle.py
python oracles/python/c4_pair_overlap_new_incidence.py --native /tmp/new-incidence-native.txt
python tools/make_proof_bank.py --check
```

The tests retain uncertain geometric boundaries and distinguish proved
carrier exclusion from state/iteration/weight exhaustion. They reject
omitted repeated edges, relabelled states, forged charts/carriers,
nonpositive weights and non-strict rates. The actual same-occurrence
zero-offset diagonal subgraph is `M^2`; its Perron radius is `beta^2`, so
it refuses a spurious strict-contraction certificate. Removing the compact
Haar factor is also calibrated as incorrect: Euclidean scaling alone
would multiply the true contraction rate by four at depth two.

Native replay and full oracle parity have passed locally on the pinned
Mojo version. Hosted exact-head CI and independent human review are
separate statuses recorded in the evidence and pull request; neither is
inferred from the local runs. No Lean formalization of F0--F5 is claimed.

The finite carrier removes a finiteness uncertainty for this specific
paired-overlap construction. It does not prove that a strict subinvariant
vector always exists, that every source in the standing PIP regime has
zero cross-letter overlap, that a critical SCC has positive overlap,
that the BPA terminates, or that arbitrary counterexamples yield finite
strict components. Corollary F5's modular-matrix route remains unimplemented.
No general C4, G1, BH, A1', strong coincidence, degree-one tiling, PDS or
PSC status is promoted.
