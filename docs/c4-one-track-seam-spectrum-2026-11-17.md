# Neutral odd multiplicities from legal one-track seams

**Status:** Written conditional identification of the strict bigon
spectrum and exact bounded Mojo computation of its inputs. Independent
review is pending. The uniform neutral-weight exclusion remains open.

[Targeted literature check](c4-one-track-seam-spectrum-literature-2026-11-17.md)

## Work shown

### Assumptions and hypotheses

Use the normalized unit PIP3 setting of
[PR #598](c4-periodic-overlap-returns-2026-11-17.md). When coincidence
rank is two and a strict system exists, write $Z$ for its joining,
$C$ for its unique swap-invariant aligned nonproductive overlap
component, $A_C$ for its occurrence matrix, and $N$ for the strict
bigon occurrence matrix. The two matrices commute with their
respective track swaps. A superscript $-$ indicates the swap-odd
sector. The spectrum statements below concern algebraic multiplicity.

The cell alphabet records both labels and the relative integral
start. Its original ordered rows are the actual positive-width
child intersections, with repeats retained. A boundary of a cell
belongs to the top track, the bottom track, or both. If a boundary
belongs to one track, the other track's tile contains it strictly
in its interior.

### Derivation / reduction

**Lemma (complete one-track adjacency set).** In $C$ every adjacent
pair of cells in $Z$ occurs inside an inflated row. To obtain all
adjacent types, start with each consecutive pair in every one-step
row and close under the map
$$
(s,t)\longmapsto (g_R(s),g_L(t)),
$$
where $g_R$ is the last and $g_L$ the first physical child.
To obtain top-only seams, keep only top-only births and stop an
inherited seam when it becomes shared.

Inflating a cell splits its interval into its ordered child cells.
A new adjacency is either inside that row or across the boundary of
two inflated adjacent cells. This proves completeness within all
iterates of individual cells. Every such word is represented in $Z$
by inflation invariance and the realization of $C$. Conversely,
each adjacent pair in $Z$ occurs with bounded gaps by compact
minimality. A sufficiently inflated cell contains a whole copy.
The track owning a boundary keeps a vertex there through inflation.
Thus a shared seam cannot later be top-only, and a bottom-only seam
cannot become top-only. Discarding these seams cannot lose a
top-only descendant at that position. Distinct adjacency types
share a single index, with a first recorded birth or inheritance.

**Theorem (cycle correction).** Let $\mathcal L$, $\mathcal R$,
and $\mathcal U$ be the cycle lists of the top-only left endpoint
map, top-only right endpoint map, and top-only legal adjacency
map, respectively. Record each cycle once by its length. For each
primitive root $\zeta$ of order $d\ge1$, the additive correction
to the algebraic multiplicity in either swap sector is
$$
b_d
=\#\{q\in\mathcal U:d\mid q\}
-\#\{q\in\mathcal L:d\mid q\}
-\#\{q\in\mathcal R:d\mid q\}.
$$
In particular,
$$
m_{N^-}(+1)=m_{A_C^-}(+1)+b_1,\qquad
m_{N^-}(-1)=m_{A_C^-}(-1)+b_2 .
$$

A $q$-cycle contributes $q$ fixed types at power $n$ if
$q\mid n$ and zero otherwise, and has one eigenvalue at each
$q$th root of unity. The members of $\mathcal U$ are the
periodic legal pairs of cells at a top-only seam. By the
two-sided nested expansion of the two cells, they correspond
bijectively to the ordinary returns at that seam in $Z$.
Swapping tracks conjugates all three top-only maps with their
bottom-only versions. The two orientations are disjoint.
Consequently the ordinary trace correction from #598 is twice
the difference of the three top-only fixed counts. Its signed
trace correction is zero. Taking the half-sum and half-difference
of the ordinary and signed traces gives the stated virtual cycle
trace separately on each sector. Finite power sums determine
nonzero eigenvalue multiplicities. This also gives $b_d$ for all
$d$ without a least-common-multiple scan or a characteristic
polynomial for the seam permutations.

**Only legal cycles can make the correction positive.** Make a
bipartite graph $S$ with right-endpoint germs on the left and
left-endpoint germs on the right. Its vertices are the cyclic
top-only endpoint states and its edges are the cyclic top-only
adjacent pairs. The seam map is a graph automorphism on this
eventual range. For any primitive root of order $d$,
$$
b_d=m_\zeta(H_1(S;\mathbb C))-m_\zeta(H_0(S;\mathbb C)).
$$
Indeed the traces on edges minus vertices agree with the
difference of traces on $H_1$ and $H_0$ by the chain exact
sequence. The actions are of finite order. In particular a
forest gives a nonpositive correction at every order, including
when some components are permuted. Merely counting the connected
components would omit a possible contribution from $H_1$.

There is an equivariant embedding of $S$ in the disjoint union
of copies of the source Barge–Diamond eventual range graph
$ER(\sigma)$ indexed by the periodic integral interior states
$I$ of the other track. Place each germ at its seam, with the
top vertex at zero. If the bottom starts at $z$ relative to the
top start and its label is $b$, a left-endpoint germ records
the interior state $(b,-z)$. A right-endpoint germ with top
label $a$ records $(b,e_a-z)$. These are exactly interior
states since the boundary is top-only. On a cyclic germ,
first or last child inflation applies the interior prototile
map to that state, because the other track contains zero in
its interior throughout the cycle. A genuine adjacent pair
has the same interior state from both sides and a legal
top-track bigram. If the pair is cyclic the bigram is in
$ER(\sigma)$.

Every cyclic endpoint germ in $C$ extends to a cyclic edge:
take an occurrence in $Z$, choose the adjacent cell on the other
side of its seam and iterate at a multiple of the germ period.
The chosen germ returns each time, so the seam stays top-only.
The deterministic adjacent-pair sequence is finite and has a
periodic tail. Thus all germ labels are in the source eventual
range. The top label and the interior state distinguish each
germ on its side, and the two labels and state distinguish the
edge. This proves the embedding and equivariance for the
product of the endpoint map and the interior-state permutation.
As graph homology in degree one embeds under subgraph inclusion,
a positive $b_d$ requires a corresponding source asymptotic
cycle in this permutation of copies. This gives an upper bound
by its $H_1$ multiplicity, with the $H_0(S)$ term subtracted.
[Barge–Diamond, Theorem 4 and the eventual range](https://arxiv.org/pdf/math/0702669)

The embedding also bounds the possible periods. The period
of a cyclic germ is the least common multiple of the period
of its interior state and that of its top endpoint letter.
For a cyclic seam one takes the least common multiple with
both endpoint-letter periods. Equality follows from
injectivity of the respective encodings. Thus if all periods
in $I$ are odd and neither source endpoint map has a
two-cycle, the correction at $-1$ is zero, even with
periodic interior lifts.

**Corollary (geometric finiteness).** Under property (F) the set
$I$ is empty. A periodic top-only endpoint would yield a
periodic interior state through the calculation above, so all
three cycle lists are empty. Therefore the nonzero spectra of
the bigon and overlap matrices agree in each swap sector. In
this case the neutral test only needs the signed overlap matrix.
[Interior prototile map and (F)](c4-geometric-f-class-2026-11-16.md)

**Exact neutral test.** Choose one representative $s$ of each
orbit of the free swap $J$ on the non-diagonal carrier. The
vectors $e_s-e_{Js}$ give the odd basis. In the column for $s$,
an occurrence of the representative $t$ contributes $+1$ in
its row and an occurrence of $Jt$ contributes $-1$. Their
ordered row mates are checked before forming the matrix. The
exact algorithm takes the characteristic polynomial of this
matrix and divides by the two monic linear factors repeatedly
to obtain their algebraic multiplicities. It then adds
$(b_1,b_2)$. A negative predicted multiplicity contradicts
the conditional spectrum identity. For a neutral first defect
of weight $(m,m,m)$ the required odd multiplicity at
$\varepsilon=(\det M)^m$ is at least the rank of the defect
image. A computed smaller multiplicity excludes that size of
neutral image for the candidate component.

### Evidence and replay

`kernel/psc/one_track_seam_spectrum.mojo` reuses the screened
Perron geometry and occurrence order of the box graph. The
physical boundary masks must match at consecutive children
and must preserve existing track vertices at inherited
boundaries. The scanner retains source row and child ordinal
for a birth, or a previous adjacency index for inheritance.
It detects cycles of partially defined finite maps and uses
exact rational polynomial arithmetic for the signed matrix.
The conditional certificate checks its component is an
aligned nonproductive sink and that every row and swap stays
in the component. The default adjacency cap is $100{,}000$
deduplicated types and the dense odd matrix cap is dimension
$48$. Exceeding either, or rejected exact arithmetic, gives
no multiplicity verdict.

```sh
cd kernel
pixi run --locked mojo run -I . -I tests tests/test_one_track_seam_spectrum.mojo
```

The productive controls use the full overlap box as a source of
literal rows. Their counts are independently replayed at the
first twelve powers from the zero-fibre interior states, the
source first and last maps, and the legal seam catalogue.
The table is for the top-only orientation.

| Ordered images | First cycles | Last cycles | Adjacent seam cycles | $(b_1,b_2)$ |
| --- | --- | --- | --- | --- |
| `01/12/021` | $1,1$ | $2$ | $2,2$ | $(-1,+1)$ |
| `1/02/202` | $2,2,2$ | $2$ | $2,2,2$ | $(-1,-1)$ |
| `1/2/021` | empty | empty | empty | $(0,0)$ |
| Tribonacci `01/02/0` | empty | empty | empty | $(0,0)$ |

The replay checks recorded birth and inheritance occurrences
in these boxes. A four-cell symbolic subdivision of
$A\mapsto BAB$, $B\mapsto ABA$ has overlap odd multiplicities
$(1,1)$ and correction $(-1,0)$. Recomputing directly on the
uncut two-letter words gives $(0,1)$, as predicted. Separate
Jordan controls check double algebraic roots at both signs.

### Negative controls

In the productive `01/12/021` geometry the other track has
one periodic interior lift, and the legal top seams form a
square on left letters $\{1,2\}$ and right letters $\{0,1\}$.
Inflation interchanges the two left endpoints and fixes the
two right endpoints. The induced sign on the square cycle is
$-1$. Its $H_0$ has eigenvalue $+1$. This accounts for the
positive $-1$ correction and refutes a universal nonpositivity
claim based only on literal geometry. It has no aligned
nonproductive sink and supplies no strict-system example.
The symbolic subdivision also lies outside the PIP3 setting.
Its surviving $-1$ shows that a general subdivision identity
alone cannot exclude a neutral eigenvalue. Cap exhaustion,
invalid boundary masks and selection of a productive component
are explicitly refused.

### Non-claims / remaining gaps

This finishes the executable finite seam correction for a
supplied eligible overlap component. No tested unit PIP3
specimen has a strict component, so the final transfer to
an actual rank-two strict bigon matrix is a conditional
written proof. The next uniform obligation is to show that
the required corrected odd multiplicity is too small in
every literal candidate sink, or to exclude those sinks by
another literal constraint. The positive productive control
keeps the seam-cycle contribution relevant off (F).
