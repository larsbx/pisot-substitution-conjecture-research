# Periodic return capacity of a literal overlap component

**Status:** Written reduction and exact bounded Mojo replay. The
ordinary and exchanged counts have independent literal-word checks.
The rank-two membership and trace identities are conditional on a
strict component. Independent review and Lean formalization are
pending. Universal C4 and the neutral-weight exclusion remain open.

[Targeted literature check](c4-periodic-overlap-returns-literature-2026-11-17.md)

## Work shown

### Assumptions and hypotheses

Let $\sigma$ be a primitive irreducible ternary Pisot substitution,
$M$ its incidence matrix and $\ell M=\beta\ell$ its positive length
row. A strict system is a finite nonempty collection of unequal
irreducible balanced pairs closed under all literal factors of the
substituted words. The two sides are ordered. Coincidence of two tilings
means a common labelled tile at some nonnegative inflation level.

Write $G$ for the complete [Proposition V box graph](p1b-vertex-coincidence-box-2026-10-02.md).
Its vertices are positive-width overlaps $(a,b,z)$, with integral
bottom-minus-top displacement $z$ and physical shift $\ell(z)$.
Irreducibility makes $\ell$ injective on the rational lattice.
An edge is an indexed occurrence of a positive-width child. Keep every
edge, including parallel edges, ordered by the physical left endpoint
of its child cell. A *nonproductive* vertex has no path to an equal-label
zero-displacement overlap. An *aligned* vertex has zero displacement.
The graph stops at labelled coincidences. Stopping there cannot change
a nonproductive component or a path that never meets a coincidence.

The periodic-pair statements use $|\det M|=1$ and the
Baker–Barge–Kwapisz normalization $h:\Omega_\sigma\to\mathbb R^3/\mathbb Z^3$.
There $\Phi$ is inflation, $h\Phi=Mh$, and starts in a common fibre
differ by integral vectors. The complete box contains every periodic
interior overlap. Under coincidence rank two, Theorem W supplies the
unique strict joining $Z$ and its primitive swap-invariant bigon
substitution whenever a strict system exists.
[BBK, §§2–4](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) ·
[Theorem W](c4-rank-two-wall-2026-11-16.md)

### Derivation / reduction

**Aligned sinks.** A strict system exists if and only if $G$ has a
nonproductive sink SCC containing an aligned vertex. This is the
sink formulation of the periodic first-letter ray test in
[PR #576](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/576).
It uses neither rank nor unimodularity. In particular, only the
closures of the six ordered aligned unequal-letter roots are needed
for this existence test. One of those complete rooted closures must
be strongly connected and free of coincidences.

In the forward direction, take a sink of the literal child graph of
a strict system. Each overlap represented inside its ordered factors
has all descendants in the same set of overlaps. A child lies inside
a single balanced factor because every balanced cut is shared across
the tracks. The set is strongly connected by whole-factor enclosure.
In detail, inflate any positive-width source cell until its width is
more than twice the maximum factor length. A whole factor lies
inside, and a path of literal factors from it reaches any chosen
target factor and overlap in the sink. The overlap at every ancestor
has positive intersection because the target interval has positive
length. This is the ordered version of the existing enclosure proof.
The overlaps form a sink, have no labelled coincidence, and include
the shared starts of the factors. They lie inside the box by cycle
containment. Conversely, if the strict system was supplied at a power,
including all intermediate factor sets first makes a one-step strict
system. A coincidence at an intermediate step would persist to the
next full power.
[Whole-factor enclosure](c4-overlap-carrier-enclosure-2026-11-04.md) ·
[Ordered enclosure](c4-oriented-alignment-2026-11-04.md)

For the reverse direction, follow first-child edges from an aligned
vertex in the sink. Each preserves zero displacement. Enter a joint
periodic first-letter orbit with period $q$ and build the two legal
one-sided rays based at their shared start by iterating $\sigma^q$.
All their overlap cells lie in the sink. The same holds for the other
$q-1$ phases. Take $H$ to be a multiple of $q$ at least as large as
the maximum first-alignment depth in the sink. Every cell in a phase
inflated by $H$ has a shared cut in its closure. Inflation by $H$
fixes each phase. Its inflated cells have length at most
$\beta^H\max_a\ell(e_a)$, so every interval of twice that length contains
a shared cut. Between consecutive cuts the two words are balanced
by injectivity of $\ell$, irreducible by consecutiveness and unequal
by nonproductivity. The word lengths are bounded. Taking these blocks
from all phases gives a finite system, and every irreducible factor of
each substituted block is a block of the next phase. Thus the
reconstruction uses all literal factors.

**Proposition (periodic pair membership).** Assume rank two and a
strict component. There is exactly one nonproductive sink $C$ of $G$.
It contains an aligned vertex and is the set of overlaps represented
in $Z$. An ordinary or exchanged periodic pair with the origin
strictly inside both tiles belongs to $Z$ exactly when its central
overlap lies in $C$.

For uniqueness, any nonproductive sink can be realized by a legal
periodic pair. From each of its cells choose an interior descendant
at some fixed depth, possible once the expanded cell is longer than
two maximal cell widths. These choices stay inside the sink. A cycle
of choices gives an interior returning position. Repeating its
literal occurrences with the fixed centre yields two nested legal
tile patches whose positive common intervals exhaust the line.
The integral relative offset puts the pair in a common fibre.
Every overlap of the resulting pair lies in the sink and none can
reach a coincidence. A translation-minimal subset of its pair orbit
closure inherits these properties. Local overlaps of positive width
persist in the limit by uniform separation of unequal fibre
vertices and equality of the finite lattice types on compact
windows. At rank two every such minimal set of distinct fibre-mates
is the same: its first projection is surjective and a tiling in a
two-element fibre has only one other entry. Therefore the minimal set
is $Z$. It contains some positive overlap in both this sink and the
represented sink of $Z$. The two SCCs agree.

For membership, a pair from $Z$ has all overlaps in $C$. In the
other direction, suppose a pair periodic at a common power has
central overlap $s\in C$. Place an occurrence of $s$ in $Z$ with the
same two tile starts. Inflation by multiples of the period gives an
increasingly large agreement with the periodic pair about the
origin. Inflation invariance and closedness of $Z$ give the desired
membership. For exchanged pairs use twice the specified power.

This is stronger than the bounded-gap test. Noncoincident returns
outside $C$ can have bounded gaps, but visits of the central state
to such an SCC give no return in $Z$. Let $A_{\rm out}$ be the
occurrence matrix of all nonproductive states outside $C$.
Every recurrent SCC there loses a positive-width child from some
column, since $C$ is the unique nonproductive sink. The cell-width
row on each block satisfies $w^\top A\le\beta w^\top$ with a
strict inequality in that column. Multiplying by a positive Perron
vector gives $\rho(A_{\rm out})<\beta$. The number of off-component
returns with both tiles interior is at most
$\mathbf 1^\top A_{\rm out}^n\mathbf 1$ for either kind of return.
The exact count below removes these returns even at a small power.

**Theorem (indexed interior return count).** Let $A$ be the
occurrence matrix on non-diagonal vertices of $G$, with child rows
and parent columns. Let $J_G$ exchange the tracks. For $e=0$ use
ordinary fixed pairs and for $e=1$ pairs exchanged by $\Phi^n$.
The exact number of ordered, distinct same-fibre pairs whose origin
is inside both tiles is
$$
\operatorname{tr}(J_G^e A^n)-E_G^e(n).
$$
Here $E_G^e(n)$ counts length-$n$ paths from a state to its
$J_G^e$ image using only the first or only the last *physical*
child, with the choice made in the original row before any
restriction to a subgraph. The same formula on nonproductive states
counts noncoincident pairs. At rank two with a strict system, the
formula restricted to $C$ counts exactly the pairs in $Z$.

The literal children partition the scaled positive intersection.
At depth $n$, a path of actual indexed children determines one
of its overlap cells. A path from $s$ to $J_G^e s$ yields a cell of
the original width $w_s$ in the expanded interval of width
$\beta^n w_s$. Anchor the original cell at its later left endpoint.
The position of the returning cell relative to the expanded anchor
is $\ell(q)$ for an integral column $q$ obtained by composing the
chosen prefixes and taking the later start at each step. Placing the
original anchor at $x=-(M^n-I)^{-1}q$ makes it return. The origin
is strictly inside the original cell precisely when
$0<\ell(q)<(\beta^n-1)w_s$. The two excluded equalities are exactly
the all-first and all-last paths. A returning cell cannot have both
equalities since $\beta^n>1$.

The returning placement gives legal nested source words.
The canonical strand anchor satisfies the same return equation and
is unique by nonsingularity. Both tile starts differ integrally, so
the pair is in a common fibre. For $e=1$ concatenate
the path and its track swap to obtain the $2n$-fold nested
expansion. Swapping and inflating by $n$ preserves the two anchor
positions in exchanged order and gives the same nested pair.
Conversely the centre of any such pair takes a unique path of
positive cells, with unique local indices. Its origin cannot hit a
vertex at an intermediate level because existing vertices persist
and each tiling returns at power $2n$. Its two tracks cannot share
the central tile at any periodic phase, since iterating that
single common tile through their common period would determine
both full tilings. This justifies the deletion of diagonals for
the distinct-pair count. A common labelled tile anywhere at any
level appears in some expansion of the central overlap, by
periodicity and exhaustion. Thus nonproductivity of this root is
equivalent to noncoincidence. A path to a swap vertex belongs to one
SCC since its swapped path returns.

**Theorem (signed trace identity for the strict system).** Suppose
rank two and a strict system. Let $N$ be the primitive bigon child
matrix from Theorem W, $J_B$ its swap, and $A_C,J_C$ the matrices
on the literal overlap sink. For every $n\ge1$,
$$
\operatorname{tr}(J_B N^n)=\operatorname{tr}(J_C A_C^n).
$$
For the ordinary trace, let $L_{\rm one}(n)$ and $R_{\rm one}(n)$
count first-child and last-child returns of $C$ whose corresponding
boundary belongs to exactly one track. Let $U(n)$ count the
ordinary fixed ordered pairs in $Z$ with the origin a vertex on
exactly one track. Then
$$
\operatorname{tr}(N^n)-\operatorname{tr}(A_C^n)
=U(n)-L_{\rm one}(n)-R_{\rm one}(n).
$$

To prove the identities, the same first-and-last subtraction for
$N$ counts exactly the returns whose origin is interior to a
bigon. The common-cut code of $Z$ recovers that bigon and the
return ordinal. The overlap count instead requires both tiles
interior. These interior counts differ for ordinary pairs by
$U(n)$. They agree for exchanged pairs: if one track has a vertex
at the origin, inflation carries it to a vertex of the other
track at the origin. The same reasoning applies to a first- or
last-child path returning to the swapped state. An initial seam
belonging to one track stays a seam of that track at every step,
so it cannot return as a seam belonging only to the other.

Finally the endpoint counts for the bigon code agree exactly
with the overlap endpoint counts at shared boundaries. For
instance a first-child return of a bigon gives the first
overlap cell of its two words, aligned at the left, and a
corresponding first-child return of that cell. Conversely start
with a left-aligned overlap whose first-child map returns it to
its required orientation. Its legal paired rays are uniquely
determined by the two first letters at the common origin and
iteration through the common period $2n$. They occur as limits
of right-hand patches in $Z$ by growing an occurrence of this
cell. Consecutive common cuts give their unique first bigon.
That bigon has the required first-child return because the
whole rays have the required action. Two distinct bigons with
the same endpoint return would give the same rays and first
bigon. The right endpoint argument uses left-hand rays and
last letters. This proves both identities including their
boundary corrections.

The ordinary term $U(n)$ can also be read from $C$ without an
enumeration of bigon words. Form the finite set of adjacent cell
pairs inside iterated cell rows. Start with every adjacent pair
in a one-step row, then close under the seam map
$(s,t)\mapsto(g_R(s),g_L(t))$, where $g_R,g_L$ select the last and
first children. These are exactly the adjacent pairs in $Z$.
One inclusion follows from occurrence and inflation invariance.
For the other, any adjacent cell pair in $Z$ occurs with bounded
gaps by compact minimality and the exact local overlap labels.
A sufficiently inflated cell therefore contains a whole copy
of it. This supplies a literal finite computation of $U(n)$.
Count the resulting adjacent pairs whose seam belongs to exactly
one track and whose two based cells return at power $n$. An
ordinary periodic pair at that seam gives one such adjacent
pair. Conversely the returning adjacent cells have left and
right intervals that grow away from zero. Their nested words
determine a unique pair in $Z$ with the specified seam.

Every term of the ordinary correction is periodic in $n$. The
endpoint maps have finite eventual cycles. A periodic tiling
with a vertex at the origin has base class zero, since its
based lattice vertex is fixed by $M^k$ for some $k>0$ and
$M^k-I$ is nonsingular. The finite zero fibre is permuted by
inflation, so $U(n)$ is periodic as well. Thus the even and odd
nonzero spectra of $N$ and $A_C$ agree away from roots of unity,
by the generating functions of their trace power sums. At a
neutral eigenvalue $\varepsilon=\pm1$ the difference of odd
algebraic multiplicities is exactly
$$
\frac{1}{2D}\sum_{n=1}^{D}\varepsilon^{-n}
\bigl(U(n)-L_{\rm one}(n)-R_{\rm one}(n)\bigr)
$$
for a common period $D$ of the correction and $\varepsilon^n$.
The signed identity determines the difference of even and odd
multiplicities without this correction. These are constraints
from the actual overlap alphabet of $\sigma$, applicable at
the neutral weights of the round-three obstruction. If the first
defect has eigenvalue $\varepsilon$ in that sector, the required
odd multiplicity is at least the rank of its nonzero image,
since that image is an intertwining quotient of the odd sector.

### Evidence and replay

`kernel/psc/periodic_overlap_returns.mojo` builds the complete
exact box and counts walks in its recurrent SCCs. Each adjacency
ordinal retains multiplicity and is replayable as two actual
image indices. The track swap is verified on every row before
counting. Dynamic programming keeps the original first and last
choices even when one leaves the SCC. The code checks arithmetic,
refuses a capped graph, and aborts if the bounded walk count
exhausts its work allowance. It uses the screened ternary field
and requires a unit matrix.

```sh
cd kernel
pixi run --locked mojo run -I . -I tests tests/test_periodic_overlap_returns.mojo
```

The independent calculation expands $\sigma^{2n}$, enumerates
its literal interior marks, and computes the $n$-step action
from each mark's struck ancestor block. It groups the resulting
ordered pairs by exact integral residue, including the zero
class. It agrees with the canonical graph at every listed
power. Entries count ordered distinct pairs with both tiles
interior, prior to testing noncoincidence.

| Substitution | Ordinary at $n=1,2,3,4,5$ | Exchanged at $n=1,2,3,4,5$ |
| --- | --- | --- |
| `1/2/021` | 0, 0, 12, 0, 10 | 0, 0, 0, 8, 10 |
| `01/12/021` | 0, 0, 6, 12, 50 | 0, 4, 30, 24, 40 |
| Tribonacci `01/02/0` | 0, 0, 6, 0, 0 | 0, 0, 0, 8, 0 |
| `1/02/202` | 0, 2, 0, 18, 0 | 2, 0, 8, 0, 32 |

All these pairs reach a labelled coincidence. The graph has no
nonproductive sink on any of the four specimens. The earlier
per-fibre replays supply further checks on the four- and
five-element classes of the first two controls.

### Negative controls

- At power two, `1/2/021` has only one fixed tiling, as given by
  Theorem FP. Both round-three abstract rows require an interior
  self-return at that power. The replay checks the complete
  second rows of $S_3$ and its swap in both orders. The independent literal address scan
  and the overlap graph each give zero distinct ordinary pairs
  with both tiles interior. The sole fixed tiling also rules out
  any distinct pair using an origin seam. At power three the
  twelve ordinary pairs are genuine but all productive, so counting
  distinct pairs alone would overstate strict capacity.
- For `1/02/202` the integer interior states of the zero fibre
  are exchanged at odd powers and fixed at even powers. They give
  two zero-class pairs in the corresponding column. Omitting the
  zero class or merging it with the seam count changes the answer.
  The independent scan also sees exchanges between different torus
  classes and excludes those from the table.
- The edge replay checks the exact local ordinals after swapping
  both tracks, parallel edges and original endpoints that leave a
  recurrent SCC on `1/02/202`. Nonunit input, the reducible unit strict control
  `1/012/101`, and both kinds of cap are refused. In the reducible
  length-one geometry of `012/120/201`, physical cuts can have
  unequal Parikh prefixes, so rational independence is substantive.

### Non-claims / remaining gaps

The complete overlap decision is per substitution. An abstract
child matrix alone does not certify an overlap component. A uniform
argument excluding aligned nonproductive sinks, or excluding the
required neutral odd multiplicity in each possible literal sink,
remains necessary for universal C4. The finite tests contain no
unit Pisot example with a strict component. The signed and ordinary
trace comparisons with an actual rank-two bigon system therefore
remain written conditional results. The verifier counts pair returns
with two interior tiles. The finite one-track seam calculation is
specified above and awaits an executable replay.

**Update 2026-11-17.** Added after #598; the text above is unchanged.
The [one-track seam spectrum follow-up](c4-one-track-seam-spectrum-2026-11-17.md)
implements that calculation by cycle counts and gives the resulting
conditional odd multiplicities at both unit roots.
