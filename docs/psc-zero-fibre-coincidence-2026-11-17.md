# PSC from a single reference in the zero fibre

Base revision `3e6995beb7ea9d8c330d1366452756f93a0ac12a`.

## Work shown

### Assumptions and hypotheses

Use a primitive substitution on $d\ge 2$ letters whose incidence
characteristic polynomial is irreducible over $\mathbb Q$ and Pisot.
Write $M$ for incidence, $\beta>1$ for inflation and $\ell$ for the
positive length row. The faithful irreducible strand normalization
uses the integer coordinate lattice $\mathbb Z^d$ and the inverse-limit
solenoid of $M$ on $\mathbb R^d/\mathbb Z^d$. It allows non-unit
determinant. The tilings considered in the zero fibre belong to the
legal minimal hull. This hull is aperiodic since a periodic legal word
would have a rational frequency column $f\ne0$, with $Mf=\beta f$ and
$\beta$ irrational. The one-letter symbolic case is trivial.

### Targeted literature decision

Proceed with the comparison of one legal periodic strand with the
complete list of legal periodic vertex and interior patches over the
identity of the solenoid. BBK Definition 4.1, Theorem 4.2 and Remark
4.3 already give coincidence rank and its algorithmic determination
by edge states at a specified torus class. Corollary 5.2 is the spectral
implication. Barge–Kwapisz Proposition 3.2 uses inflation-periodic
two-letter joins, and Proposition 17.1 uses literal overlap reachability.
Barge–Diamond's eventual range gives exactly the periodic legal seams.
Minervino–Thuswaldner Proposition 9.7 gives the finite zero-expansion
graph in the non-unit representation. The repository already uses the
periodic integer half-open state map and its certified box. The target
here is the one-reference test on complete legal strands for every
determinant, with a finite seed comparison for each member of the fibre.
[BBK 2006](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf)
· [Barge–Kwapisz 2006](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf)
· [Barge–Diamond 2008](https://arxiv.org/pdf/math/0702669)
· [Minervino–Thuswaldner 2014](https://arxiv.org/pdf/1402.2002)

The proof must retain every based interior state when property (F)
fails. The unit specimen `01/12/021` already has a fixed interior state.
For non-unit incidence, the identity of the solenoid specifies every
level, including the negative levels. Reducible or singular controls
fall outside the rank-to-spectrum scope.
[FC2 rank transfer](c4-fc2-rank-transfer-review-2026-11-16.md)
· [(F) state map](c4-geometric-f-class-2026-11-16.md)

### Derivation / reduction

For a finite labelled patch $P$, write $\Phi^n P$ for the exact edges
of its $n$-fold inflation. An occurrence of $b$ in $\sigma^n(a)=U b V$
takes $(a,x)$ to $(b,M^n x+p(U))$, where $x$ is the initial vertex and
$p$ counts letters. Call two patches coincident if their equally
inflated patches share a labelled edge at some depth $n\ge0$. A
depth-zero hit persists at a positive depth by nonerasure.

**The zero-fibre criterion.** Form a catalogue $\mathcal P$ as follows.

1. For each periodic legal bigram $ab$ under
   $ab\mapsto\operatorname{last}(\sigma(a))\operatorname{first}(\sigma(b))$,
   take the pair of edges $(a,-e_a),(b,0)$ joined at the origin.
2. For every based periodic state $(a,v)$ of the half-open prototile
   map with $0<\ell(v)<\ell(e_a)$ and $v\in\mathbb Z^d$, take the edge
   $(a,-v)$.

For *any* reference patch $P_*$ in the catalogue, the geometric
coincidence rank is one exactly when

$$
\forall Q\in\mathcal P\quad \exists n\ge0:\quad
\Phi^n P_*\cap\Phi^n Q\ne\varnothing
\quad\text{as sets of labelled edges.}
$$

More generally, the rank is the clique number of the graph on
$\mathcal P$ joining pairs with no such common descendant. Each vertex
belongs to a clique of that size. BBK Corollary 5.2 gives pure discrete
spectrum of the tiling flow exactly in the rank-one case. BBK's invariant
measure is supported on the legal hull. For the symbolic formulation,
Clark–Sadun Corollary 3.2 gives a constant-roof suspension conjugate to the
Perron-length flow, since only one incidence eigenvalue has modulus at least
one. For a roof of height $c$, the time-$c$ map acts as the shift on the
base and the identity on the height. Pure discrete flow spectrum thus
implies pure discrete shift spectrum. Conversely, a shift eigenfunction
$f(Sx)=e^{2\pi i\theta} f(x)$ gives suspension flow eigenfunctions
$f(x)e^{2\pi i(\theta+k)u/c}$ for $k\in\mathbb Z$, where $u$ is height.
For each $f$ these span its height subspace by Fourier completeness.
[Clark–Sadun](https://arxiv.org/pdf/math/0201152)

**Completeness of the catalogue.** In BBK's irreducible normalization
$\Sigma=\Gamma=\mathbb Z^d$, so the type corrections vanish in Definition
3.1. A strand orbit over the identity has integral vertices at every
stage. Its fibre is finite by Theorem 4.2 and is invariant under the
invertible shift of stages. Every member is therefore periodic under
inflation. The positive functional $\ell$ is injective on rational
vectors. Otherwise the rational span of the incidence iterates of a
nonzero vector in its kernel is a nonzero proper invariant subspace,
contrary to irreducibility. Consequently the edge containing the
length-zero cut either starts at the origin or contains it strictly in
its projected interior. In the first case use the edge ending there as
well. A period of the strand must return this seam to itself, so its
legal bigram is periodic. In the second case the containing edge is
$(a,-v)$, and a period returns the deterministic containing-edge state
$(a,v)$ to itself. The update is $(b,Mv-p(U))$ at the unique occurrence
whose half-open interval in $\sigma(a)=U b V$ covers $\beta\ell(v)$.

Conversely, if a catalogue patch returns at period $p>0$, then
$P\subseteq\Phi^pP$. The inclusion for a seam identifies the last and
first image edges at zero, and for an interior state it is exactly the
periodic-state equation. All the finite paths $\Phi^{jp}P$ have the
same inner edges as the preceding path. Their left and right outer
ends expand away from zero by $\beta^{jp}$. The union is a full strand
and is fixed by $\Phi^p$. Every finite subword of the union is legal,
since the original seam is legal or the seed is a single letter. The
stable positions of all descendants are uniformly bounded. In an
adapted stable norm with contraction factor $\rho<1$, each inflation
applies $M$ and adds one of the finitely many proper prefix vectors.
The resulting stable norm bound is geometric. The periodic phases
therefore lie in BBK's cylinder, by its eventual absorption property.
All phases have integer vertices. Taking the phases modulo $p$ gives
the complete orbit over the solenoid identity, including its negative
stages. This construction is inverse to reading the origin patch from
a legal member of the fibre, since its nested finite paths already
cover the whole strand. Equal periodic stage-zero strands give equal
complete orbits by taking a common multiple of their periods.

The legal seam list is finite. For the interior list, let $D$ bound
the stable norm of a projected proper prefix vector. The largest
stable norm $B$ on a periodic state cycle satisfies $B\le\rho B+D$.
The cut condition also bounds $\ell(v)$ by the largest tile length.
Together these bounds give a finite integral box. Each coordinate
bound can be computed with the Perron row and the non-Perron eigen-rows
over algebraic numbers. One may use rational outer bounds and exact
sign comparisons. A periodic state stays in the box for its entire
cycle. A legal bigram exists because some image has at least two
letters, and the seam map preserves the finite set of legal bigrams.
Its eventual range is nonempty. These facts ensure the catalogue can
always supply a reference.

**A maximal separated family through every legal strand.** At a point
of the generic set of BBK Theorem 4.2 the fibre consists of $r$ pairwise
noncoincident strands, where $r$ is the coincidence rank. The point can
be chosen to avoid the images of the finitely many exceptional
translation orbits outside the minimal hull. In the zeroth torus
coordinate the image of each such orbit is a translated line, hence
Haar-null for $d\ge2$. The projection of the solenoid onto that torus
is a surjective homomorphism, so the original orbit image is also
Haar-null. Thus all $r$ strands can be chosen legal.

Fix any legal strand $T$. By minimality the first of the generic
strands has translates converging to $T$. Pass to a common subsequence
of these translations along which all $r$ strands converge. Their
limits lie in one fibre by continuity. Noncoincidence is preserved
for this family. If two limits share a labelled edge at an inflation
level, at that level the approximating strands have edges with the
same label and with starting vertices converging to its start.
The differences of those starts lie in $\mathbb Z^d$, since each
approximating pair is in a common fibre. The differences are then
eventually zero, contradicting the noncoincidence of that pair. This
gives $r$ pairwise noncoincident legal strands through $T$, counting
$T$ among them. There can be no larger such family in its fibre by
Definition 4.1. This argument uses the topology of the complete
strand space and the discrete lattice, as in the compactness step
of BBK Theorem 4.2.

**From the strands to literal finite comparisons.** A common
descendant of two patches is also an edge in the inflated strands.
Conversely, suppose some inflation of the two strands shares a
labelled edge. Write the two inflated strands as the increasing
unions of their inflated seed paths, using a common positive period.
The shared edge belongs to both finite paths at some sufficiently
large common multiple of the period. Thus the graph on patches is
exactly the noncoincidence graph on the legal zero fibre. The preceding
maximal-family result gives both assertions about cliques. If $r>1$,
every reference has a noncoincident partner, proving the stated
rank-one test. The proof does not use transitivity of eventual
coincidence. A chain of individual hits is insufficient.

For a fixed substitution the depths may also be padded to one common
depth for every comparison. Once two patches share an edge, each further
inflation preserves a shared descendant. Take the largest depth over the
finite catalogue and then round it up to a multiple of all the periods.

If the reference has period $p$, a cycle of period $q$ only needs one
comparison per residue class modulo $\gcd(p,q)$ in its phase order.
For the associated strands, simultaneous inflation preserves eventual
coincidence in both directions. A witness at any positive level can be
propagated forward past any prescribed level by nonerasure. Simultaneous
inflation by $p$ fixes the reference and advances the other strand by
$p$ phases. Its orbits in the $q$-cycle are the stated residue classes.
The executable retains every based phase and calculates its own depth.

**The remaining literal condition.** To decide an individual
comparison, start with any two edges of the two seed patches whose
projected interiors intersect. A labelled edge of positive width
can be shared later only among descendants of such an overlapping
pair. If $z$ is the bottom start minus the top start, the actual
child displacement is $Mz+p(V)-p(U)$ for the selected top and
bottom prefixes $U,V$. A state with letters $a,b$ survives only if
$-\ell(e_b)<\ell(z)<\ell(e_a)$. The stable displacement stays
bounded by contraction and the bounded prefix differences, and
the displayed strict inequalities bound the length coordinate.
All reachable $z$ are integral, so the exact graph is finite.
A path composes the chosen letter occurrences, and the diagonal
is equal letters and $z=0$. In the cubic implementation equality
of the exact Perron-field displacement implies integral equality
by the injectivity of $\ell$. Neither reduction replaces the
solenoid with its zeroth coordinate.

**On property (F).** The interior list is empty. A seam $ab$ is
coincident with $a'b'$ exactly when $a,a'$ are right strongly
coincident or $b,b'$ are left strongly coincident, allowing equality
in each relation. Opposite-side edges touch at zero and cannot
share a positive-width descendant. Same-side edges use the terminal
or initial anchoring convention respectively. In particular, on
three letters a known good pair on each side defines the complementary
hub on that side. If a legal periodic seam has no legal periodic
seam whose two hub-membership bits are both complementary, that seam
is coincident with every member of the catalogue, proving rank one.
This test uses the actual legal two-letter joins.

In any alphabet, a periodic seam that shares its first or second letter
with every periodic seam proves rank one under (F). In particular, if
there are precisely two periodic letters on each endpoint side, rank
greater than one forces the periodic seam set to be closed under switching
both coordinates to their other values. Otherwise a seam without its
opposite would meet every seam by equality on at least one side. If the
eventual-range graph on these four endpoint vertices is connected, it must
contain all four seams in the rank-greater-than-one case. A connected graph
on the four vertices uses at least three edges, and simultaneous switching
makes the number of edges even.

**A finite obstruction in the graph of all strict overlaps.** In the
irreducible class, BBK Remark 4.3 also gives a criterion without choosing
a reference. Take any strict integral overlap with labels $a,b$ and
starts $0,z$ for $z\in\mathbb Z^d$. Translate both edges along the unstable
line so that the stable hyperplane intersects both projected interiors.
The two starts have the same torus class since their difference is
integral and the type corrections vanish. The translated edges belong to
one of BBK's state sets $S_q$. Translating them together preserves all
labelled coincidences, since the common translation at depth $n$ is
multiplied by $M^n$. Conversely, two states in the same $S_q$ differ by an
integral start vector. Both contain the cut under the left-closed,
right-open convention, hence their projected interiors intersect to the
right of the cut. Therefore $\mathrm{cr}=1$ if and only if every strict
integral overlap reaches an equal-label, zero-displacement state. This
uses the edge-state rank theorem of Remark 4.3 directly. The periodic
catalogue above gives a second criterion with fewer required seed
comparisons. [BBK 2006](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf)

For any fixed strict overlap its whole reachable set is finite. Indeed,
for $D$ as in the prototile bound, one child obeys
$\nu(z')\le \rho\nu(z)+2D$. The reachable set stays inside
$\nu(z)\le\max\{\nu(z_0),2D/(1-\rho)\}$ and $|\ell(z)|$ is bounded by
the largest tile length. A root fails to reach a diagonal if and only if
it belongs to a finite set of strict overlaps, closed under **all**
literal overlapping children and free of diagonals. For the forward
direction use the reachable set itself. For the reverse direction every
finite path stays in the set. The existence of one such set anywhere in
the full integral graph is equivalent to $\mathrm{cr}>1$ by the preceding
application of Remark 4.3.

Every strict overlap has a child. In the scaled parent intervals, the
larger of the two left endpoints lies in both left-closed, right-open
intervals. Select the child that contains it in each image. Their
interiors have a nonempty common interval immediately to the right of
that point. Choose a state of minimum stable size $K$ in a finite closed
set. Any child belongs to the set and has size at most $\rho K+2D$.
Therefore $K\le\rho K+2D$ and $K\le 2D/(1-\rho)$. The intersection of the
closed set with this smaller strip is nonempty and closed under children
by the same bound. The resulting universal obligation is to exclude a
nonempty diagonal-free child-closed set in that strip with the strict
projected overlap bounds. A path from a specified root to a bad component
only establishes failure at the component. The global criterion can use
any member of the component as its root.

### Evidence and replay

The comparison routine in `kernel/psc/zero_fibre.mojo` uses the first
lexicographic periodic legal seam as reference. Its exact arithmetic
domain admits primitive irreducible Pisot cubics with images of length
at most six, subject to the certified box and checked arithmetic.
It reuses `legal_two_words`, `eventual_range` and the certified periodic
state box. It searches the joint exact overlap graph from the finite seed
pairs and computes the minimum successful depth for each patch. The
overlap search stops at a first coincidence along each path. The default
overlap state limit is 20,000 and the periodic state limit is the existing
`GEOMETRIC_F_STATE_CAP`. A completed search with no path reports depth
`-1`. An exceeded cap, uncertifiable box, invalid input or integer
arithmetic failure raises.

From `kernel/` with the pinned Mojo environment active, replay with

```bash
mojo run -I . -I tests tests/test_zero_fibre.mojo
```

The regression expands the literal substituted words in $\mathbb Z^3$,
checking that each seed returns at its reported first period, that a hit
occurs at its reported depth and that none occurs at any earlier depth.

| Images of $0,1,2$ | $\det M$ | Reference seam | Periodic seams | Interior phases | Largest first-hit depth |
| --- | ---: | --- | ---: | ---: | ---: |
| `01/02/0` | 1 | `00` | 3 | 0 | 0 |
| `01/12/021` | 1 | `10` | 4 | 1 | 4 |
| `1/012/001` | 2 | `10` | 4 | 8 | 8 |

The unit interior cut of `01/12/021` is $(2,(-1,0,1))$ and hits at depth
1. For determinant two the eight phases belong to one cycle of period
8. Their first-hit depths in the reported phase order are
`5, 6, 6, 8, 5, 6, 6, 4`.

**Lean interface.** `PscVerif.ZeroFibreOverlap` reuses `IntegralEdge`,
`EdgeDescendant`, `EdgeCoincident`, `LengthData` and `ContractionData`.
`edgeDescendant_succ_iff` uses the existing `locateSubst` lookup to
recover a literal source occurrence and local digit. It needs neither
matrix inversion nor irreducibility. `edgeDescendant_bounds` proves
strict overlap pulls back through all levels. The checked patch
predicate is

```lean
def PatchCoincident {α : Type*} [DecidableEq α] [Fintype α]
    (s : α → List α) (reference patch : List (IntegralEdge α)) : Prop :=
  ∃ e ∈ reference, ∃ f ∈ patch, EdgeCoincident s e f
```

Here a seam is `[(a, -pvec [a]), (b, 0)]` and an interior patch is
`[(a, -v)]`. `patchCoincident_iff_overlap_reach` uses the strict roots
of each patch pair and allows a path to stop at its first diagonal.
The witness has one common depth, label and integer starting point.
`overlap_reach_finite` applies the existing contraction data to the
difference of the two proper prefixes. For a specified root,
`overlap_not_productive_iff_closed` identifies failure with a finite
closed set containing that root and avoiding the diagonal.
`all_overlaps_productive_iff_no_bounded_closed` gives the uniform strip
criterion using `strictOverlap_exists_child`. Its theorem takes a bound
on all prefixes of the letter images. The child estimate uses only
proper prefixes. The contraction-data
construction and periodic-state finiteness theorem are already in
`GeometricFPisot`. The fibre and spectral steps use the cited theorems.

From `proof/PscVerif/`, use the pinned Lean and Mathlib revisions and run

```bash
lake build PscVerif.ZeroFibreOverlap
```

### Negative controls

Both the unit and nonunit examples with interior phases would have an
incomplete catalogue if only their seams were retained. They also refute
strengthening the target to a shared edge whose projected interior contains
the origin. The origin remains a vertex of the inflated reference seam
at all depths. It stays strictly inside a tile of the inflated interior
seed, since the containing-edge state is periodic and a vertex state
would be absorbing. Their verified hits are away from the cut.
`touching_edges_not_coincident` checks the endpoint-only control in Lean. The
regression requires the nonunit example to refuse each cap set to one.
The reducible substitution `10/102/211` is refused before a rank verdict.

### Non-claims / remaining gaps

The remaining universal obligation is to exclude a nonempty set in the
bounded strip that contains no diagonal and is closed under every
literal overlapping child. Equivalently, for the chosen legal periodic
seam and each patch in the catalogue, find literal occurrences of a
common label at a common depth $n$ in the images of some edges of those
two patches. With starts $x,y$ and prefixes $U,V$, their witness equation
is

$$
p(U)-p(V)=M^n(y-x).
$$

The words $U,V$ must be prefixes up to those occurrences in the actual
images $\sigma^n(a)$ and $\sigma^n(b)$. The finite graph decides this for
an admitted individual substitution after a complete run. A universal
proof of this reachability assertion is pending. PSC, universal C4 and the
existing strict-system obligations remain open. The fibre reduction is a
written proof pending review. The replay covers the three named fixtures
and refusals. The Lean module proves the abstract graph contract. A
machine proof of the geometric and spectral imports, and verification
of a concrete Mojo graph through that contract, remain separate.
