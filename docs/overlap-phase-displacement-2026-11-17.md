# Displacements in cyclic phases of closed literal overlap graphs

**Status:** Written phase-displacement proof with a Lean-checked seven-offset bound from the stated sign and connectivity hypotheses.

## Targeted literature check

The proposed constraint is that each cyclic phase of a finite closed
strongly connected component has zero as a strictly positive weighted
average of its integral displacements. In a component without any
aligned starts, the same offsets form a connected unit-step lattice
graph. The proposed cardinality bound uses both facts.

| Source | Interface used |
| --- | --- |
| [Baker–Barge–Kwapisz, Remark 4.3](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | Computes coincidence rank using same-class edge states, including the non-unimodular setting. The irreducible full lattice gives the integral coordinates used here. |
| [Akiyama–Lee, §4 and Theorem 4.1](https://arxiv.org/pdf/1003.2898) | Uses complete occurrence counts and coincidence-leading and residual overlap graphs. Local subdivision and spectral radius alone allow a full-growth residual. |
| [Bufetov–Solomyak, §§2–3](https://pure.mpg.de/rest/items/item_3121415_1/component/file_3121417/content) | Uniform frequencies for primitive substitution tilings. The proof below derives the needed finite-window limit directly by counting supertiles. |

The repository already proves exact forward mass conservation and has a
mean-offset argument for oriented balanced pairs under additional
hypotheses. Here the observable is the full integer start displacement of
an elementary overlap, sampled by length in each literal cyclic phase.
[Ordered overlap mass](c4-overlap-mass-2026-11-10.md)
· [Closure attempts §3](c4-closure-attempt-2026-11-16.md)

Proceed with the phasewise displacement constraint and the finite lattice
bound. Retain the known productive recurrent overlap cycles as controls
for the closure premise. An alignment-free diagnosis uses all literal
children and tests zero displacement separately from the diagonal.

## Work shown

### Assumptions and hypotheses

Let $\sigma$ be primitive on $d\ge2$ letters. Its incidence matrix $M$
has irreducible Pisot characteristic polynomial, and its positive length
row $\ell$ satisfies $\ell M=\beta\ell$. A state $(a,b,z)$ denotes
the positive-width intersection of the top $a$-tile starting at $0$
and bottom $b$-tile starting at $z\in\mathbb Z^d$. Physical coordinates
are obtained by applying $\ell$. A literal child is one occurrence in
each expanded tile with positive-width intersection. Displacements are
bottom minus top. Irreducibility gives injectivity of $\ell$ on
$\mathbb Z^d$. A diagonal has $a=b$ and $z=0$. An aligned state only
requires $z=0$.

Let $C$ be a finite nonempty strongly connected component closed under
every literal child, and let $C_0,\ldots,C_{h-1}$ be its cyclic phases.
Displacement centring holds for every such component. The support
bounds assume $C$ is diagonal-free.

### Derivation / reduction

**Theorem.** For every cyclic phase $C_i$ there are real weights
$\mu_q>0$ for **all** $q\in C_i$, summing to one, such that
$\sum_{q\in C_i}\mu_q z(q)=0$. In a diagonal-free component, every
nonzero real linear functional takes both signs on each phase. The
distinct offsets form a connected graph with edges given by unit
lattice steps $\pm e_a$. Each phase has at least $2d+1$ distinct
offsets. A phase that omits $0$ has at least $2d+2$.

**Literal subdivisions in one phase.** Fix any root of $C$ and its
positive-width intersection $J_0$. At depth $n$, the common interval
$J_n$ is scaled by $\beta^n$. The overlay of the two actual words
partitions $J_n$ into the positive-width intersections of their tiles.
Their labels and displacements are exactly the length-$n$ child
occurrences, counted with multiplicity. For the backward direction,
each pair in this partition has unique actual ancestor occurrences and
their inflated intervals contain the pair's positive-width cell.
Consequently each ancestor pair is strict. This is the literal
path-to-patch interface of the zero-fibre proof. Every depth-$n$ cell
is in phase $C_i$ for the depth residue associated to that phase.
[Zero-fibre overlap proof](psc-zero-fibre-coincidence-2026-11-17.md)

Fix a phase and choose a positive $k$ divisible by $h$ such that each
state of that phase has every state of the phase as a depth-$k$ child.
Such $k$ exists by primitivity of the period-$h$ return block. Write
$w_q>0$ for the physical width of state $q$ and $w_{\max}$ for the
maximum width in $C$. At level $n$ in that phase, with $n\ge k$,
each cell at depth $n-k$ contributes at least one cell of any specified
type $q$ in the phase. Its total inflated width is at most
$\beta^k w_{\max}$. Thus the width fraction of type $q$ throughout
$J_n$ is uniformly bounded below by $w_q/(\beta^k w_{\max})$.

**Uniform one-track frequencies on these intervals.** On either track
take any fixed depth $r$ and the partition into depth-$r$ supertiles
in the depth-$n$ word. The length fractions of those types in $J_n$
converge to the same vector on the two tracks. Indeed, for fixed $m$
one can first use complete depth-$(r+m)$ supertiles. The two end
fragments have total length at most $2\beta^{r+m}\max_a\ell_a$.
Within a complete depth-$(r+m)$ tile of type $c$, the fraction of type
$a$ at depth $r$ is

$$
\frac{\ell_a(M^m)_{a,c}}{\beta^m\ell_c}.
$$

The Perron–Frobenius limit is uniform in the finitely many $c$ and
independent of $c$. First take $n\to\infty$ for the end fragments and
then $m\to\infty$ for this uniform limit. The argument also gives
equality in the limit for the average of any fixed bounded function
repeated inside each depth-$r$ supertile according only to its type
and its local physical coordinate. Replace the function by its integral
average on each complete depth-$r$ supertile. End effects within such
supertiles vanish for fixed $r$ as $|J_n|$ grows.

**Mean displacement.** For almost every $t\in J_n$, let $X(t)$ and
$Y(t)$ be the actual lattice starts of the top and bottom tiles
containing $t$. On a cell their difference $Y-X$ equals its state
offset. The physical component $\ell(Y-X)$ is the top tile age minus
the bottom tile age, where the age of a tile starting physically at
$s$ is $t-s$. The preceding one-track limit with $r=0$ gives a common
limiting average age. The physical mean displacement therefore tends
to zero.

Let $P_s$ be the stable projection whose kernel is the Perron line.
Use an adapted stable norm with $\|M_s\|\le\rho<1$. All track starts
at all levels have bounded stable norms, say at most $K$. A stable
start is obtained by repeatedly contracting the parental start and
adding a proper prefix vector from one of the original images. The
geometric series for these bounded digits gives $K$, including the
fixed initial starts. Within a depth-$r$ supertile, the stable start
of a letter is the stable start of that supertile plus the stable
projection of a local prefix of $\sigma^r(c)$. The former term has
norm at most $\rho^rK$, since the supertile start is $M^r$ applied to
the start in the depth-$(n-r)$ word. The latter term is a bounded
function depending only on the supertile type and its local position.
By the one-track limit its averages on the two tracks agree in the
limit for fixed $r$. Thus the limsup of the norm of the difference
of stable averages is at most $2\rho^rK$. Let $r\to\infty$. Together
with the physical limit this gives

$$
\frac{1}{|J_n|}\int_{J_n}(Y(t)-X(t))\,dt\longrightarrow 0.
$$

Take a subsequential limit of the finite vector of depth-$n$ width
fractions in the fixed residue class. Its entries sum to one and the
uniform lower bound above makes every entry of the phase positive.
The integral identity gives the claimed mean for that limit.

**Every coordinate changes in a diagonal-free phase.** For any letter
$a$, sufficiently long $J_n$ contains a full occurrence of $a$ in its
interior on the top track. To see this, choose a fixed power of $\sigma$
whose image of every letter contains $a$. An interior interval longer
than three supertiles of the maximum length at that power contains a
complete interior supertile. At the end of this $a$-tile, the top
start advances by $e_a$. If the bottom track also crosses a boundary,
the ending bottom tile cannot be labelled $a$. Otherwise equal right
endpoints and equal lengths give equal starts and a diagonal in the
preceding positive-width cell. Hence the $a$ coordinate of the offset
decreases by one at that event, with or without a simultaneous bottom
boundary. It is nonconstant within the phase. A strictly positive
centred average forces a positive and a negative value of this
coordinate.

**Unit-step connectivity.** At an interior boundary of the overlay, a
one-track event changes the displacement by $\pm e_a$. A simultaneous
event always produces $z=0$ in the cell immediately to its right.
If the phase omits $0$, a sufficiently deep single overlay word visits
all phase states with unit changes between consecutive offsets. If the
phase contains $0$, choose $n$ large enough that the depth-$(n-k)$
overlay has at least two cells. The first inflated cell contains $0$
and the second contains every phase state. For any nonzero offset
visited in the second, take the segment of the walk since its last
preceding zero. No simultaneous event occurs on that segment, since
such an event would create a later zero. This gives a unit-step path
from $0$ to the offset. Connectivity uses the spatial order of the
literal subdivided interval.

A connected unit-step support with both signs in each coordinate
has a step of each direction, so its affine span is $\mathbb R^d$.
If a nonzero linear functional had only nonnegative values on that
support, the strictly positive centred weights would force it to
vanish on the whole support. This contradicts the full affine span.
Apply the same argument to its negative. In particular zero lies
in the interior of the convex hull in each diagonal-free phase.

**Cardinality bound.** Let $S$ be the distinct offsets and choose a
spanning tree of the finite connected unit-step graph. For each
coordinate, a tree path from a minimizer to a maximizer uses at
least the coordinate range in edges of that direction. The ranges
are at least two because the offsets are integral and take both
signs. Each tree edge contributes to exactly one direction. Thus
$|S|-1\ge\sum_a(\max_S z_a-\min_S z_a)\ge 2d$.

If $|S|=2d+1$, each direction uses exactly two tree edges, and its
coordinate range consists of $-1,0,1$. The path from a negative to a
positive vertex uses both edges of that direction. Removing those
two edges leaves a connected middle zero set and two terminal
subtrees on which that coordinate is $-1$ or $1$. Aggregate the
positive weights $\mu_q$ by offset. The two terminal subtrees have
equal weight by centring of the coordinate, and each has weight less
than $1/2$ since the middle subtree has positive weight.

Choose a weighted median vertex of the tree, a vertex for which each
branch after its removal has weight at most $1/2$. Such a vertex
exists by minimizing the weighted sum of tree distances. Moving
one edge towards a branch of weight greater than $1/2$ strictly
reduces that sum. If the median belonged to either terminal subtree
for a coordinate, the branch towards its complement would contain
weight greater than $1/2$. Thus the median has zero in every
coordinate and $0\in S$. This proves the extra unit in the lower
bound when the phase omits $0$.

In particular a ternary hypothetical closed obstruction needs at
least seven distinct integral offsets in every phase and eight in
each phase with no aligned state. Distinct labels sharing an offset
count only once. The same lower bounds apply to the number of typed
states in each corresponding phase.

### Evidence and replay

The new Lean theorem `Psc.PhaseDisplacement.card_of_both_signs` proves
the $2d+1$ cardinality bound from a connected unit-step graph and both
signs in each coordinate. It constructs a spanning tree. For each
coordinate the cuts at $-1$ and at $0$ each give a crossing edge. A
unit-step edge crosses at most one of these cuts, so the chosen edges
are distinct. The tree has one fewer edge than vertices. The theorem
takes the signs and connectivity as hypotheses. The phase-centering
proof, the derivation of those hypotheses for literal overlaps, and
the stronger median step are written arguments above.

From `proof/PscVerif/` run

```bash
lake build PscVerif.PhaseDisplacement
```

The Mojo diagnostic finds cyclic phases of a supplied recurrent
subgraph using the repository's exact period and cyclic-class
functions. It deduplicates displacements and traverses all available
unit steps using exact addition and subtraction of letter-length
vectors in the cubic field. The traversal gives integral relative
coordinates and their widths when the support is connected. It
checks the width budget and the extra lower bound for a phase that
omits zero. A successful result meets the measured necessary
conditions. A capped input raises because its phase inventory is
incomplete. To apply the exclusion result, the caller must also use
a literal closed component of the full graph in the theorem's regime.

From `kernel/` with the pinned Mojo environment run

```bash
mojo run -I . -I tests tests/test_overlap_phase_displacement.mojo
```

### Negative controls

The abstract support containing zero and the six signed coordinate
vectors has size seven. An eight-point zero-free support is given by
the planar path $(-1,0),(-1,1),(0,1),(1,1),(1,0),(1,-1)$ at third
coordinate zero, and the two neighbours $(1,0,\pm1)$. In that order
the positive integer weights $6,1,1,1,1,3,1,1$ give mean zero before
normalization. These attain both combinatorial bounds. The fixture
also checks that two labelled states at the same offset count once.

A separate seven-point connected zero-free support has width two in
each coordinate. Its points satisfy $x\le y$ with strict inequality
somewhere, so it lacks a strictly positive centred average. Its
rejection exercises the extra lower bound beyond the width check.

For the PIP3 substitution `000122/01/0`, the actual overlap with both
labels $0$ and displacement $e_1$ has a self-loop. Its one-vertex
recurrent subgraph has one distinct offset. The exact graph gives
a diagonal descendant at depth two. Thus recurrence by itself cannot
supply the closure hypothesis. With the graph cap set to one, the
diagnostic refuses a phase verdict.

### Non-claims / remaining gaps

A finite closed obstruction would have a sink component subject to
these bounds. The bounds alone leave larger literal supports open.
A seven-offset ternary phase necessarily contains zero and lies in
$\{-1,0,1\}^3$. A corresponding aligned state has unequal labels and
could still belong to a strict component. The next obligation is
to derive a literal exit or a contradiction for the remaining
supports in the bounded strip. Universal C4, PSC and coincidence
rank one in general remain open. The combinatorial controls are
support examples, with no claim of realization by a substitution.
