# Critical components of the exact paired-overlap measure equation

**Status:** written proofs at the stated finite-matrix scope; independent
human mathematical review pending. The eigencone classification is the
classical Frobenius--Victory theorem, specialized here to the authenticated
paired-overlap equation. Canonical Mojo execution and independent full
packet reconstruction certify the twelve-source calculation in section 8.
These finite checks are separate from the written measure and eigencone
proofs. No general C4, G1, BH, A1', SC, PDS or PSC status is promoted.

The [targeted literature gate](c4-critical-overlap-components-literature-gate-2026-11-05.md)
records the prior-art and hypothesis check before implementation. The
starting equation and finite-carrier hypotheses are those of
[F0--F5 in the preceding note](c4-finite-overlap-carrier-2026-11-05.md),
inspected at PR #497 head
`837b34b8a511c9bcfcb2030e2ece5e27d9991282`.

## 1. The equation, graph orientation and scope

Let `T` be a finite nonnegative matrix and let `theta>0`. Throughout,

```text
T v = theta v,                 v >= 0.                    (1)
```

An edge `i -> j` means `T_ij>0`: a row points from a parent state to a
child whose coordinate contributes to that parent's equation. For the
paired-overlap application, `T_ij` is the number of retained actual
paired occurrences with target `j`, `theta=beta^q`, and
`v_i=mu(E_i)`. Repeated occurrences must retain their multiplicities.
The graph must contain complete rows, with every omitted child proved
empty by the source construction. An arbitrary adjacency list does not
inherit that geometric interpretation.

Let `S` denote a strongly connected component (SCC), let `A_S=T[S,S]`
be its principal block, and write `rho_S=rho(A_S)`. Its outgoing forcing
is

```text
b_S = sum_{D != S} T[S,D] v_D >= 0.
(theta I-A_S) v_S = b_S.                                  (2)
```

The component graph is a finite directed acyclic graph. A component `S`
is an *ancestor* of `C` when `S` reaches `C`; the component itself is
included. A *proper ancestor* is different from `C`. A *strict descendant*
is reached from a component and is different from it. These directions
are fixed by the row convention above and are not interchanged.

Call a component subcritical, critical or supercritical according as
`rho_S<theta`, `rho_S=theta` or `rho_S>theta`. A singleton with no self-edge
has block `[0]`; it is subcritical because `theta>0`.

The statements below concern the exact equality (1). A one-sided bound
such as `theta v <= T v` does not supply the same conclusions. For example,
`T=[3]`, `theta=2`, `v=[1]` satisfies that inequality despite positive
mass on a supercritical block.

## 2. Support and the three component rules

**Lemma CE1 (support propagation; written proof, human review pending).**
For any solution of (1), positivity propagates backward along graph paths,
and zero propagates forward. Within an SCC, either all coordinates are
zero or all are positive.

*Proof.* If `T_ij>0` and `v_j>0`, then
`theta v_i=sum_k T_ik v_k >= T_ij v_j>0`. Conversely, if `v_i=0`, the
nonnegative sum in its row is zero, so every target of a positive edge
from `i` has zero coordinate. Iterate along paths. Mutual reachability
gives the SCC assertion.

**Lemma CE2 (component trichotomy; written proof, human review pending).**
For every nonnegative solution of (1):

| Internal spectral radius | Consequence |
| --- | --- |
| `rho_S>theta` | `v_S=0`, and every descendant of `S` has zero coordinates. |
| `rho_S=theta` | `b_S=0`; every strict descendant of `S` has zero coordinates. On `S`, `v_S` is a nonnegative multiple of its positive Perron vector. |
| `rho_S<theta` | `v_S=(theta I-A_S)^(-1)b_S`. The inverse is entrywise positive, so `v_S=0` exactly when `b_S=0`; otherwise every coordinate on `S` is positive. |

*Proof.* For an SCC block choose a positive left Perron vector `u`, so
`u^T A_S=rho_S u^T`. For the singleton zero block use `u=[1]`.
Pairing (2) with `u` gives

```text
(theta-rho_S) u^T v_S = u^T b_S >= 0.                     (3)
```

If `rho_S>theta`, the left side is nonpositive. Equality requires both
`u^T v_S=0` and `u^T b_S=0`. Strict positivity of `u` and nonnegativity
of the two vectors imply `v_S=b_S=0`. Lemma CE1 propagates zero to every
descendant.

If `rho_S=theta`, equation (3) gives `b_S=0`. Every outgoing edge from
`S` to a different component therefore has zero target coordinate, and
Lemma CE1 propagates that zero to every strict descendant. On `S`,
equation (2) is the Perron eigenvector equation. Its nonnegative solutions
are the nonnegative multiples of one positive Perron vector, including
the zero multiple.

If `rho_S<theta`, the convergent Neumann series gives

```text
(theta I-A_S)^(-1)
    = sum_{n>=0} theta^(-n-1) A_S^n.                       (4)
```

All entries are nonnegative. For each ordered pair of vertices of `S`,
some internal path contributes a positive entry to a power of `A_S`;
the `n=0` term handles the diagonal. Thus every entry of the inverse is
positive. For `[0]`, the inverse is `[1/theta]`, with the same property.
Formula (4) proves the third row of the table.

The critical rule does not require `S` to be a sink or to carry positive
mass. Its outgoing contribution vanishes for every nonnegative solution.
The supercritical rule is also stronger than an assertion about sinks of
the positive support: the block and all its descendants vanish outright.

## 3. Which critical components can support a nonnegative eigenvector?

For the fixed threshold `theta`, call a critical component `C` *eligible*
when every proper ancestor `S` satisfies `rho_S<theta`. This is the
distinguished-class condition in the classical theorem; the term eligible
records its use as a candidate for overlap mass, not geometric positivity.

Tam--Schneider, *On the core of a cone-preserving map* (1994),
[Theorem 2.1 and its definitions, printed p.484](https://people.math.wisc.edu/hans/paper_archive/scanned_papers/hs106.pdf),
give the distinguished-class characterization with the same edge
orientation. Butkovic--Schneider--Sergeev--Tam, *Two cores of a nonnegative
matrix* (2013),
[equation (6), Proposition 2.11 and Theorem 6.1](https://people.math.wisc.edu/hans/paper_archive/other_papers/hs164.pdf),
state the ordinary nonnegative-algebra version and its extremal rays.
The strict ancestor comparison is essential; the max-algebra comparison
in that paper is a different statement. The proof below makes the
specialization and support directions explicit.

**Theorem CE3 (eligible critical rays; classical theorem, written
specialization, human review pending).** Let `E_theta` be the set of
eligible critical components of `T`. For each `C in E_theta`, there is
one normalized nonnegative vector `x^C` satisfying

```text
T x^C = theta x^C,
x^C_i > 0  exactly when the component of i reaches C.     (5)
```

Normalize its restriction to `C` to have coordinate sum one. Then

```text
{v>=0 : T v=theta v}
    = {sum_{C in E_theta} a_C x^C : a_C>=0}.              (6)
```

The representation is unique. These vectors generate the extreme rays
of this cone and are linearly independent. If `E_theta` is empty, the
cone consists only of zero.

*Proof: necessity.* Call an SCC active when its coordinates in `v` are
positive. Every ancestor of an active SCC is active by Lemma CE1.
For any active component, choose a sink of the active components reachable
from it. Its outgoing forcing is zero, so (2), positivity and
Perron--Frobenius show that it is critical. Hence every active component
reaches an active critical component.

Now let `C` be active and critical. Every proper ancestor is active, so
none is supercritical by Lemma CE2. No proper ancestor can be critical
either: a path from that ancestor to `C` begins with an edge into another
active component, making its outgoing forcing nonzero, contrary to the
critical rule. Every proper ancestor is therefore subcritical, and `C`
is eligible.

*Proof: construction.* Fix an eligible `C` and a positive Perron vector
`r_C` of its block with coordinate sum one. Set `x^C_C=r_C`, and set
`x^C_S=0` outside the ancestor set of `C`. Process the proper ancestors
in an order in which children precede parents. Their blocks are strictly
subcritical by eligibility, so define

```text
x^C_S = (theta I-A_S)^(-1) sum_{D != S} T[S,D] x^C_D.     (7)
```

Each proper ancestor has an outgoing edge on some path to `C`. Induction
and the positive inverse in (4) show that its resulting vector is strictly
positive. The equation on `C` holds because any outgoing component from
`C` lies outside its own ancestor set and was assigned zero. An edge
from a component outside that set into the set would make the source
component an ancestor as well. Thus there is no such edge, and every
outside component's zero equation also holds. This proves (5).

*Proof: spanning and uniqueness.* In any nonnegative solution, every
critical block is either zero or active and eligible. On an eligible
`C`, Lemma CE2 gives `v_C=a_C r_C` with `a_C>=0`. Subtract the vector
`sum_C a_C x^C` algebraically; to establish equality, use reverse
component order. The critical blocks agree, supercritical blocks are
zero in both vectors, and each subcritical block is uniquely determined
by its already determined outgoing blocks through (4). Thus every block
agrees, proving (6).

Two distinct eligible critical components cannot reach one another:
the upstream one would be a critical proper ancestor of the downstream
one. Consequently, `x^C` is zero on every other eligible critical block.
Reading a linear combination on each such block proves linear
independence and uniqueness of its coefficients. The extreme-ray claim
follows immediately from the unique nonnegative representation.

## 4. Root nullity and the danger of dropping incoming equations

**Corollary CE4 (root feasibility; written proof, human review pending).**
For a specified vertex `r`, some solution of (1) has `v_r>0` if and
only if `r` reaches an eligible critical component of the supplied graph.
If no such component is reached, every solution has `v_r=0`; in
particular the actual overlap measure is zero when (1) has been
authenticated for that overlap graph.

*Proof.* The support descriptions in (5) and the nonnegative sum (6)
give both directions for the finite linear system. Its actual measure
vector is one member of that system's cone, which supplies the stated
one-way geometric implication.

The phrase *supplied graph* is essential. Let `R` be the vertices reachable
from `r`, retaining every outgoing edge of those vertices. Then `R` is
forward closed, and an actual solution restricts to
`T[R,R]v_R=theta v_R`. Absence of an eligible critical component in this
restriction proves the root null. But presence is only feasibility of
the restricted equations. Equations at vertices outside `R` can exclude
that candidate.

For example, with vertices in the order `r,C,A`, take

```text
theta=2,
T=[[0,1,0],
   [0,2,0],
   [0,1,2]].                                             (8)
```

The root reaches exactly `{r,C}`. On that restriction, the ray
`(v_r,v_C)=(a/2,a)` is allowed. The omitted equation at `A` is
`2v_A=v_C+2v_A`, forcing `v_C=0`, hence `v_r=0`. In the full graph,
`C` is ineligible because it has the critical proper ancestor `A`;
only the ray supported on `A` remains.

For this reason, a verifier must state which complete system it checked.
It may use a forward-closed restriction for sound nullity, but cannot
equate feasibility there with feasibility after restoring omitted
incoming equations, much less with actual geometric positivity.

## 5. An outer area bound does not eliminate a surviving ray

**Corollary CE5 (positive upper bounds preserve ray feasibility; written
proof, human review pending).** Suppose `x>=0` is nonzero and
`T x=theta x`. For any finite list of strictly positive coordinate bounds
`U_i`, there exists `a>0` such that `0<=a x_i<=U_i` for every coordinate.

*Proof.* Take a positive `a` no larger than
`min_{i:x_i>0} U_i/x_i`. The index set is nonempty and finite, and every
ratio is positive.

In particular, the common upper bound `v_i<=area(Q)>0` from the preceding
overlap construction does not by itself rule out an eligible critical
ray. The actual vector can be zero even when nonzero vectors satisfy
both the graph equation and every such upper bound. Additional geometric
information, known zero coordinates or a separately justified quantitative
lower constraint may further restrict the feasible cone. None is supplied
merely by the existence of a critical SCC.

## 6. Exact polynomial exclusion for integer blocks

Now assume that `T` has integer entries and that `theta` is an algebraic
integer with monic irreducible minimal polynomial `g in Z[t]`. The source
adapter must authenticate both `g(theta)=0` and irreducibility/minimality.
An annihilator alone does not justify the degree shortcut: `theta=2`,
`A=[2]` and `g(t)=(t-2)(t-3)` would otherwise give a false exclusion.
Replacing the minimal polynomial by an arbitrary polynomial is not a
valid certificate.

**Lemma CE6 (block polynomial certificates; written proof, human review
pending).** For a square integer block `A`, any of the following proves
that `theta` is not an eigenvalue of `A`, and therefore that `A` is not a
critical SCC block:

1. `size(A)<degree(g)`.
2. `g(A)` is nonsingular over the rationals.
3. For a prime `p`, the exact matrix `g(A) mod p` is nonsingular over
   the finite field `F_p`.

*Proof.* If `theta` is an eigenvalue, its minimal polynomial divides the
integer characteristic polynomial of `A`, which proves the first
exclusion. An eigenvector `y` for `theta` satisfies `g(A)y=g(theta)y=0`,
which proves the second. A nonzero determinant modulo `p` is the reduction
of a nonzero integer determinant, proving the third.

Conversely, triangularizing `A` over the complex numbers shows that
the eigenvalues of `g(A)` are the values of `g` at eigenvalues of `A`.
Thus singularity of `g(A)` means that `g` and the characteristic polynomial
of `A` share a root. When `g` is irreducible, they share the factor `g`,
so `theta` is an
eigenvalue of `A`. This converse still does not say that `theta=rho(A)`:
the associated eigenvectors can be signed.

For the twelve-source incidence of PR #497 at graph step two,

```text
g(t)=t^3-7t^2+5t-4,
g(A)=A^3-7A^2+5A-4I.                                    (9)
```

The preceding note proves this minimal-polynomial identity. Thus no SCC
of size one or two can be critical in that experiment. More generally,
for an irreducible cubic Pisot root `beta`, `beta^q` has degree three for
every positive integer `q`: the degree divides `[Q(beta):Q]=3`; degree
one would make `beta^q` rational, and a contracting conjugate of `beta`
would then have the same `q`-th power, contradicting its modulus below
one while `beta^q>1`.

Failure at a prime is inconclusive. For (9), `A=[1]` gives `g(A)=[-5]`:
its reduction modulo 5 is singular although the rational matrix is
invertible. A prime search that exhausts its declared budget must retain
an unresolved block, rather than classify it as critical or null.

The finite-field computation must verify its input block, coefficients,
prime and elimination witness. Arithmetic, size or pivot failures must
refuse acceptance. A floating spectral approximation is not a substitute
for these exact checks.

### Complete block exclusion and safe elimination

After an SCC permutation, `T` is block triangular with diagonal blocks
`A_S`. Polynomial evaluation preserves that structure, so

```text
det g(T) = product_S det g(A_S).                          (10)
```

Different blocks may use different successful primes. If every block has
a certificate from Lemma CE6, (10) makes `g(T)` nonsingular, and the
homogeneous equation forces `v=0`. The same reasoning applies to any
authenticated forward-closed root-reachable restriction.

An isolated block certificate does **not** justify setting its coordinates
to zero. Its equation is (2), with an outgoing term that may be nonzero.
For example,

```text
theta=2, T=[[1,1],[0,2]]
```

allows `(v_0,v_1)=(a,a)`. The first block `[1]` excludes eigenvalue 2,
but its positive outgoing forcing supports its positive coordinate.

A safe partial elimination procedure starts with only independently
proved zero coordinates and applies the following sound rules:

- Propagate a known zero forward along every retained edge.
- Mark a certified supercritical SCC and all its descendants zero,
  using Lemma CE2.
- For a certified critical SCC, mark all its strict descendants zero,
  while leaving the SCC itself unresolved unless another rule applies.
- When all outgoing coordinates of a block are already zero, a
  certificate excluding eigenvalue `theta` makes its homogeneous block
  equation invertible and proves the block zero. Process such blocks in
  reverse component order or iterate these rules to a fixed point.

Each update has its own zero proof, so induction proves the soundness of
all marked coordinates. Unmarked coordinates remain unresolved; the
procedure is not a positivity algorithm. An exact certificate that
`rho_S != theta` also suffices in the final rule by (3), even if `theta`
is another, non-Perron eigenvalue of the block. Modular nonsingularity is
one sufficient exclusion method, not a complete spectral classifier.

For comparison, exact positive-vector tests can certify the trichotomy:
on an SCC, `A w<=theta w` with `w>0` and at least one strict coordinate
implies `rho(A)<theta`; the reversed inequality with one strict coordinate
implies `rho(A)>theta`; exact equality implies `rho(A)=theta`. Pairing
with the positive left Perron vector proves each implication. Such tests
need exact algebraic sign/equality checks and are separate from merely
finding a modular singularity.

## 7. Countercontrols and what each protects

The following are finite-matrix calibrations. They are not asserted to be
actual Pisot substitution overlap graphs.

| Threshold and matrix | Nonnegative solutions of `T v=theta v` | Required distinction |
| --- | --- | --- |
| `theta=2`, `T=[[1,1],[0,2]]` | `(a,a)`, `a>=0` | A noncritical block can carry positive outgoing-forced mass. |
| `theta=2`, `T=[[3,1],[0,2]]` | Only zero | A supercritical ancestor excludes a reachable critical block; a global strict weight certificate is unavailable. |
| `theta=2`, `T=[[2,1],[0,2]]` | `(a,0)`, `a>=0` | A critical ancestor excludes the downstream critical block, but need not vanish itself. |
| `theta=2`, `T=diag(2,1)` | `(a,0)`, `a>=0` | An unreachable critical component cannot support the second root. |
| `theta=2`, `T=[[3,1],[1,3]]` | Only zero | Eigenvalue 2 exists, but its eigenvectors are signed; the Perron root is 4. |
| `theta=2`, `T=[0]` | Only zero | A trivial SCC is handled without a cycle exception. |
| Cubic `g` from (9), `A=[1]`, `p=5` | `g(A)=-5` over the integers | A bad prime is an inconclusive modular attempt. |
| Matrix (8) and its root restriction | Full graph forces `v_r=0`; restriction permits `v_r>0` | Removing incoming equations enlarges linear feasibility. |

The second example is a strict increase in the scope of the equality-based
argument: any positive `w` has `(Tw)_0>3w_0`, so no bound
`Tw<=lambda w` with `lambda<2` can hold, yet the exact nonnegative
eigencone is zero. This is an algebraic control, not new finite-domain
coverage of the PSC corpus.

The supplied occurrence matrix and SCC partition must be authenticated
before applying any of these methods. Missing repeated edges can change
both spectral radii and the eigencone. A claimed partition that splits a
genuine SCC can conceal the critical block; one that joins unrelated
components is not entitled to the irreducible-block Perron arguments.

## 8. Executed twelve-source certificate

The canonical implementation is
[`kernel/psc/c4_overlap_scc_obstruction.mojo`](../kernel/psc/c4_overlap_scc_obstruction.mojo),
with a [complete packet driver](../kernel/c4_overlap_scc_obstruction.mojo)
and [native regression](../kernel/tests/test_c4_overlap_scc_obstruction.mojo).
The [independent oracle](../oracles/python/c4_overlap_scc_obstruction.py)
rebuilds the same complete occurrence graphs without reading the earlier
global positive weights. No local spectral witness is supplied for these
twelve sources either: every block is excluded algebraically.

Each source has images `11/middle/last`, with source index
`2*middle_index+last_index` in the displayed order. The common exact scale
is `theta=beta^2`, with minimal polynomial (9) and
`63/10<theta<32/5`.

| Index | Middle / last | SCC count | Singleton degree exclusions | Other SCC sizes |
| --- | --- | ---: | ---: | --- |
| 0 | `012 / 01` | 3,518 | 3,516 | 5, 143 |
| 1 | `012 / 10` | 3,259 | 3,258 | 391 |
| 2 | `021 / 01` | 3,518 | 3,516 | 28, 123 |
| 3 | `021 / 10` | 3,031 | 3,027 | 3, 3, 12, 622 |
| 4 | `102 / 01` | 3,564 | 3,561 | 15, 21, 56 |
| 5 | `102 / 10` | 3,516 | 3,514 | 34, 119 |
| 6 | `120 / 01` | 3,057 | 3,053 | 3, 3, 12, 622 |
| 7 | `120 / 10` | 3,525 | 3,523 | 28, 123 |
| 8 | `201 / 01` | 3,492 | 3,490 | 34, 119 |
| 9 | `201 / 10` | 3,554 | 3,551 | 15, 21, 56 |
| 10 | `210 / 01` | 3,256 | 3,255 | 391 |
| 11 | `210 / 10` | 3,503 | 3,501 | 5, 143 |
| **Total** | **12 sources** | **40,793** | **40,765** | **28 blocks** |

All 40,765 singleton SCCs are excluded by the authenticated cubic degree.
Some singletons have self-edges; acyclicity is not assumed. Each of the
28 remaining blocks has full-rank `g(A)` over `F_101`. The largest is
622 by 622, below the declared matrix budget 768. The deterministic prime
budget is `[101,103,107]`; no fallback beyond 101 was needed. Every rank,
determinant residue, member list and condensation row is recorded in the
[exact receipt and complete native packet](../evidence/c4-critical-overlap-components-2026-11-05/README.md).

Lemma CE6 and the block-triangular identity (10) therefore exclude
`theta` from the spectrum of each complete graph. The only solution of
`T v=theta v` is zero. In particular all **43,915** state coordinates,
including the **36** distinct-letter zero-offset roots, have zero measure
under the preceding note's exact overlap equation. All **253,395** repeated
occurrence edges are retained. This recovers the twelve-source null-overlap
and scoped strict-system exclusion by an alternative certificate; it adds
no new substitution to the previously certified finite class.

The calculation does not label every component subcritical. Excluding
one algebraic eigenvalue and comparing the Perron radius are different
tasks. The earlier positive-weight proof remains valid and independently
gives its stronger uniform contraction bound. The new equality-based
rules can also handle the supercritical-ancestor controls in section 7,
where such a global strict contraction certificate cannot exist.

### 8.1 Independent algorithms and authentication

Mojo uses vendored iterative Tarjan SCCs, exact prime-field arithmetic,
sparse occurrence-based Horner evaluation, and row elimination. Python
uses iterative Kosaraju, integer matrix powers before reduction, and
elimination on the transpose. Small actual blocks are also checked with
integer fraction-free determinants and permutation expansion. Both
authenticate the supported minimal polynomial before degree exclusion.
The implementation supports the specific cubic scale and the rational
calibration `theta=2`; it does not compute a general algebraic eigencone.

Complete packet parity compares every state, repeated edge, SCC member,
condensation edge, modular attempt and zero flag. It checks **210,252**
records, not only summaries. The uncompressed native packet is 6,346,587
bytes with SHA-256
`3d3681a85a5b4f1bc4cca5839c5fe2ac37a91ab50b9014e947b984d020a4037d`.
The native regression reaches its final contract receipt; all **29**
independent/adversarial oracle tests pass with the native packet supplied.
Exact-source command records are archived with the evidence.

### 8.2 Refusals and review findings retained

The native source-0 cap of 4 leaves its size-5 and size-143 blocks
unresolved. The independent source-3 cap of 512 leaves its size-622 block
unresolved. Neither case consumes the old weight certificate as a hidden
fallback. A failed prime, including `g([1])=0 mod 5`, remains inconclusive.
The actual diagonal matrix `M^2` has a verified positive critical vector
and is correctly left allowed. Its six-dimensional doubled control
`[[M^2+I,I],[I,M^2+I]]` has the algebraic eigenvalue `theta` only on signed
vectors and a larger Perron radius; validated positive supercritical
witnesses force its nonnegative `theta`-eigencone to zero.

Source review found that the first Python draft returned mutable cached
graphs, allowing an altered graph to corrupt its own authentication
reference. The accepted implementation caches immutable source snapshots
and serialized analyses, returning defensive reconstructions. Regression
tests delete all 21,151 source-0 edges through a returned graph and mutate
a returned report; both altered certificates are refused and the expected
reference remains unchanged. All accepted certificate data are
reauthenticated by the repaired verifier.

The complete native and oracle limits are explicit: at most 20,000 graph
states, 81 occurrences per row, 20,000,000 component-pair normalization
scans and 768 rows per dense block. Exhaustion is refusal or unresolved
status, never a theorem. The local pinned compiler is a restored minimal
installation; hosted CI separately uses the fresh locked Pixi environment.
Local success does not stand in for a hosted CI result.

## 9. Remaining mathematical target

The general outcome of this note is a precise description of what the
finite measure equation permits. No eligible critical component is
assumed absent for an arbitrary Pisot substitution. No surviving ray is
identified with positive actual overlap measure. No tiling, Meyer,
open-set, degree-one or geometric realization hypothesis is supplied by
the eigencone calculation, and no general extraction of a finite strict
balanced-pair system is established. For a new complete graph with a
surviving eligible critical ray, useful additional work must address that
ray: derive an occurrence-compatible zero constraint, an incompatible
normalization/lower bound, or a new structural exclusion. Merely shrinking
strictly positive upper boxes cannot remove the ray by Corollary CE5.

A subsequent context check found the separately reported
[physical-mass continuation in issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461#issuecomment-6655681747).
It proposes an additional source-derived premise `T^t H<=theta H`, `H>0`.
Under that premise, a critical SCC has no incoming edges in our `T`
orientation: apply the positive Perron pairing to the corresponding block
of `T^t` and its nonnegative slack. Every vertex of the complete source
graph is reachable from a declared root, so a component with no incoming
edge must contain a root. Thus that additional premise would reduce
criticality testing to at most three source SCCs per substitution and
exclude supercritical SCCs entirely. These are source SCCs of `T`, or
terminal SCCs of `T^t`; confusing the directions would invalidate the
reduction.

The useful next implementation target is therefore to authenticate that
physical-mass premise from the literal source occurrences and track-swap
normalization, then reuse exact component exclusions on the reduced
inventory. The separately reported Python experiments on the eighteen
sources of PR #496 are not native evidence for this PR, and neither that
physical premise nor those artifacts are consumed by the present result.
The current all-component certificate and the general CE1–CE6 proof remain
valid without them.
