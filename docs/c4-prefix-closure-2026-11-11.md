# C4: literal prefix closures and complete incoming occurrences

The [pre-code source gate](c4-prefix-closure-literature-2026-11-11.md)
was committed as `9f2814b137e031740ae8c1efcedb74afeae22937` before this
implementation began. This step builds on the
[actual matrix-adic carrier](c4-madic-residue-2026-11-11.md) from PR #541.
The introducing pull request records the accepted source revision and
the observed complete Lean, axiom, native, oracle, and governance
receipts. This document makes no numerical test-count or acceptance
claim in place of those receipts.

**Advance:** define the sets from literal prefixes of a supplied
right-infinite word, prove their exact incoming set equation, and pass
that equation to their closures under a continuous closed action. On the
actual product with the matrix-adic carrier, this supplies the tile
equation that the previous occurrence-cover bridge required as a premise.
The word, its period, the realization maps, and the topological hypotheses
remain explicit.

Compactness requires a separate compact window containing all stable
prefix coordinates. An intended Pisot stable realization and its prefix
bound, complete finite ancestor-domain representation, nonunit
product-Haar scaling, a measure recurrence, and strict-cut positivity are
not established by the prefix equation. C4, global G1, Concentration, and
the general Pisot Substitution Conjecture remain unproved. No governed
claim status is promoted.

## 1. The word and the exact growth hypothesis

Let `tau : Fin 3 -> Word`, and let `w : Nat -> Fin 3` be a right-infinite
word. For each natural number `n`, put

\[
P(n)=w[0,n),\qquad b(n)=|\tau(P(n))|.
\]

The full fixed-prefix condition is

\[
P(b(n))=\tau(P(n))\qquad\text{for every }n.          \tag{1}
\]

The coverage hypothesis is cofinality of the expanded prefix lengths:

\[
\forall m\;\exists n,\quad m<b(n).                 \tag{2}
\]

If `tau` is nonerasing, every parent contributes at least one letter, so
`b(n) >= n`. Taking `n = m+1` proves (2). Keeping (2) in the general core
also permits erasing substitutions whose expanded prefixes remain
unbounded. Zero-length parent blocks have no local marks.

Condition (1) alone is insufficient. If every substitution image is
empty, both sides of (1) are empty for every `n`, even for `w = 000...`.
There are then no output occurrences, and (2) fails. This control is
directly relevant to the raw equation, not merely to a termination
argument.

### A constructed word from a productive seed

The existing
[`FixedPointLimit`](../proof/PscVerif/PscVerif/FixedPointLimit.lean)
construction supplies an actual word when a finite seed `U` is a prefix
of `tau(U)`, its expansion is strictly longer, and `tau` is nonerasing.
Successive iterates form a nested prefix chain. Nonerasure preserves the
nonempty added suffix, so the lengths grow without bound. The limit is
defined by the stable letters of that chain; `limit_fixed_eq` gives
(1), rather than replacing it with a finite collection of tested prefixes.
Nonerasure supplies (2) for the resulting word.
The new `PrefixAddress.seedWord` wrapper exposes these premises directly;
`seedWord_fixedPrefix`, `seedWord_cofinalImages`, and `seedWord_spec`
connect the constructed word to its complete finite iterated seed
windows.

For `tau = sigma^k`, the same argument can be expressed using
`FixedPointLimit.limit` at period `k`, with
`U` a strict prefix extension under `sigma^k` and the required nonerasing
premise. `Binomial.subst_power` binds the finite block substitution to
that iterate. A native certificate may validate these finite seed and
substitution premises; the generic Lean theorem, rather than a bounded
experimental search, supplies the infinite-word conclusion.
Strict seed growth is a sufficient premise of this constructor, not a
necessary condition for an infinite fixed word. For example, the identity
substitution has fixed words and cofinal expanded prefixes, although it
cannot satisfy this constructor's strict-growth test.

## 2. Occurrence addresses are preserved before taking a set image

The source interface is
[`PrefixAddress.lean`](../proof/PscVerif/PscVerif/PrefixAddress.lean).
`childIndex_injective` needs neither fixedness nor cofinality;
`childIndex_surjective` needs cofinality; `complete_address` adds the
fixed-prefix premise to obtain the prefix and selected-letter identities.

For each parent ordinal `i`, a local full mark

\[
d:\operatorname{Mark}(\tau(w(i)))
\]

contains the actual `before`, selected `letter`, and `after` words and
their decomposition of the parent image. Its global output position is

\[
\operatorname{address}(i,d)=b(i)+|d.\mathrm{before}|. \tag{3}
\]

The map in (3) is injective for the concatenation of all parent blocks.
Under (2), every natural output position has an address. A sufficiently
large finite substituted prefix witnesses the lookup, and the existing
literal `locateSubst` uniqueness identifies the parent and local mark.
Under (1), the selected output agrees with the supplied word, and

\[
\begin{aligned}
m&=b(i)+d.\mathrm{index},\\
w(m)&=d.\mathrm{letter},\\
P(m)&=\tau(P(i))\,d.\mathrm{before}.                \tag{4}
\end{aligned}
\]

Consequently the address correspondence retains parent ordinal, local
index, and the full literal split. Two equal parent letters at different
positions remain different records. So do repeated local letters or
equal prefixes in different image words. Abelianization and projection
are applied only after this correspondence has been established.

Taking the set of projected points can collapse many records. In
particular a zero star map identifies all projected prefixes, and a
finite residue map can identify many different prefixes. Neither set
equality nor profile-cardinality equality asserts equality of occurrence
multiplicities. The count-bearing address records remain available
separately from set support.

## 3. The raw prefix-point equation

[`PrefixClosure.lean`](../proof/PscVerif/PscVerif/PrefixClosure.lean)
defines `raw`; its `raw_tileEquation` proves the equation below, and
`tileEquation_iff_iUnion` exposes the finite full-mark union.

Let `G` be an additive commutative group, with additive maps

\[
\star:\mathbb Z^3\longrightarrow G,\qquad A:G\longrightarrow G,
\]

and require

\[
A(\star z)=\star(M_\tau z)\quad\text{for every }z.  \tag{5}
\]

The integral incidence action uses column vectors. Define

\[
\operatorname{Raw}_c
  =\{\star(\operatorname{parikhZ}P(n)):w(n)=c\}.     \tag{6}
\]

Let `D_c` be the finite type of all incoming literal digits `(a,d)` with
`d : Mark(tau(a))` and `d.letter = c`. From (4), additivity of
abelianization, and (5), obtain

\[
\operatorname{Raw}_c
 =\bigcup_{(a,d)\in D_c}
    \{A x+\star(\operatorname{parikhZ}d.\mathrm{before}):
          x\in\operatorname{Raw}_a\}.              \tag{7}
\]

For the forward inclusion, address the position defining a point of
`Raw_c`. For the reverse inclusion, a parent prefix occurrence and its
chosen local mark construct the global output position in (3). The
selected-letter identity proves that it contributes to `Raw_c`.

This step needs (1), (2), and (5). It needs no topology, compactness,
injectivity, primitivity, irreducibility, Pisot property, or measure.
Equation (7) is a set union. It neither proves disjointness of branch
images nor deletes repeated incoming occurrences.

## 4. Passing to closures without presupposing compact tiles

Give `G` a topological additive-group structure, and define

\[
K_c=\overline{\operatorname{Raw}_c}.                 \tag{8}
\]

Assume that `A` is continuous and a closed map. The pinned Mathlib
theorem `IsClosedMap.closure_image_eq_of_continuous` gives

\[
\overline{A(S)}=A(\overline S).
\]

Translations are homeomorphisms, and the incoming-digit type is finite.
Thus closure of (7) gives

\[
K_c=\bigcup_{(a,d)\in D_c}
    \{A x+\star(\operatorname{parikhZ}d.\mathrm{before}):x\in K_a\}.
                                                               \tag{9}
\]

This is the literal `OccurrencePiece.TileEquation` for the sets defined
in (8). The general source theorem is `closure_tileEquation`; the
defined-family wrapper is `prefixTiles_tileEquation`, with separate
nonerasing and productive-seed wrappers. The relevant pinned closure,
finite-union, and product APIs and
their primary sources are listed in the
[source gate](c4-prefix-closure-literature-2026-11-11.md).

A closed embedding is a sufficient stronger condition on `A`; it also
gives injectivity needed when identifying inverse-overlap pieces. No
compactness premise on the tiles is required for this route. Conversely,
continuity alone provides only one of the image/closure inclusions and
does not justify the general image/closure step used to derive (9).

## 5. The actual product carrier and period scale

Let `M` be the incidence action of `sigma`, and retain the actual carrier
from [`MadicResidue`](../proof/PscVerif/PscVerif/MadicResidue.lean):

\[
H_M=\varprojlim_q\mathbb Z^3/M^q\mathbb Z^3.
\]

Write its integral map as `iota`, its action as `T`, and its coordinate
maps as `rho_q`. For injective `M`, the implemented carrier is compact
Hausdorff and `T` is continuous and injective. A continuous injection
from a compact space to a Hausdorff space is a closed embedding.

Supply a topological additive group `E`, an additive closed embedding
`B : E -> E`, and an additive `pi : Z^3 -> E` with

\[
B(\pi z)=\pi(Mz).
\]

Then on the actual product set

\[
G=E\times H_M,\quad
\star z=(\pi z,\iota z),\quad
A(e,h)=(Be,Th),                                    \tag{10}
\]

the action is a closed embedding, and (5) holds at the original scale.
The relevant new interfaces are `madic_action_isClosedEmbedding` and
`ambientAction_isClosedEmbedding`.
This construction uses the genuine integral quotient carrier. It does
not identify it with the unrestricted completion-field representation
used in nonunit Rauzy-tile literature.

If the word is fixed under `tau = sigma^k`, use the literal image words
of `tau`, incidence `M^k`, and action `A^k`. The fixed-prefix equation and
closure equation are proved at that scale. No one-step equation for
`sigma` is inferred solely from a period-`k` word. All residues remain in
the same carrier `H_M`; the relevant detector is its level `k`:

\[
\rho_k(A^k x)=0,\qquad
\rho_k(\star z)=0
 \quad\Longleftrightarrow\quad z\in M^k\mathbb Z^3. \tag{11}
\]

Here `rho_k` ignores the `E` coordinate. Formula (11) gives exact
integral range reflection for the block substitution. The converse
integral-lift implication follows from commutation by taking the star
image of an integral preimage. Neither an isomorphism with `H_(M^k)` nor
injectivity of the canonical map `iota` is assumed. The latter can have a
kernel even when `M` is injective.
`ambient_block_reflectsIntegralRange` states the range-reflection result;
`ambient_prefixTiles_tileEquation` retains `k`, the actual word, its full
fixed-prefix equation, and cofinality in the closure-equation statement.

## 6. Sound incoming covers and finite residue exclusions

For a packet `p = (a,b,z)`, use the existing positive-prefix overlap

\[
O(p)=K_a\cap(K_b+\star z).
\]

With `tau`, `A^k`, and the defined prefix closures from (8), a literal inverse record
retains two incoming full marks and an integral ancestor packet `u`
satisfying

\[
M^k u.\delta
 =p.\delta+
   \operatorname{parikhZ}d_b.\mathrm{before}
   -\operatorname{parikhZ}d_t.\mathrm{before}.       \tag{12}
\]

Action injectivity, commutation, and (12) identify its paired branch
intersection with the affine image

\[
A^k O(u)+\star(\operatorname{parikhZ}d_t.\mathrm{before}).
\]

The closure tile equation covers all paired branches. The actual residue
detector in (11) makes nonintegral paired intersections empty. Therefore
the existing incoming-cover theorem applies to the defined prefix
closures, with every literal record retained. Iterating it gives a cover
at every prescribed finite history depth. Under integral-action
injectivity, the existing finite bound is

\[
\#\operatorname{History}(\tau,n,p)
 \leq \left(\left(\sum_a|\tau(a)|\right)^2\right)^n. \tag{13}
\]

Finiteness at each prescribed depth does not bound the union of ancestor
states over all depths. Restricting the cover to a supplied finite domain
still needs the existing representation premise at every represented
intermediate source, or a proved exact retained-union criterion. Incoming
coverage does not establish forward completeness.
The new direct wrappers are `ambient_prefix_overlap_cover` and
`ambient_prefix_finite_history_cover`. The restricted-domain statement
continues to use the existing conditional cover interface.

The complete level-`k` digit profile is

\[
C_c=\{[\operatorname{parikhZ}d.\mathrm{before}]_k:
          (a,d)\in D_c\}.
\]

The established block equation and (11) imply

\[
\rho_k(K_c)\subseteq C_c.                           \tag{14}
\]

This applies the existing `OccurrenceResidue.image_tile_subset_blockProfile`
to `ambient_prefixTiles_tileEquation`. Likewise, the existing
`image_tile_eq_blockProfile` and `overlap_empty_of_blockProfile_separation`
supply the equality and exclusion consequences under their stated
premises. These are applications of existing interfaces, not a claim of
additional newly named profile proofs in this step.

Every residue in the profile is attained if every contributing parent
tile is nonempty. A sufficient word-level premise is that every letter
appears somewhere in `w`, since the corresponding raw set then has a
point. Without such a premise only the enclosure (14) is asserted.

For the sign convention above, a sound overlap exclusion is

\[
C_a\cap(C_b+[z]_k)=\varnothing
\quad\Longrightarrow\quad O(a,b,z)=\varnothing.    \tag{15}
\]

Complete finite profile computation can now be connected to the defined
prefix closures under the explicit hypotheses. The profile is an outer
support, not a count of occurrences or a measure. A failed separation
test does not prove nonempty overlap. A successful separation test does
not establish that every exclusion made by a larger finite constructor
has been justified.

## 7. Compactness and the minimal remaining geometric lemma

Suppose `E` is Hausdorff and supply a compact subset `C` with

\[
\forall n,\quad
\pi(\operatorname{parikhZ}P(n))\in C.                \tag{16}
\]

Every raw tile lies in `C x H_M`. This product is compact and closed;
each closure in (8) is a closed subset of it. Hence every `K_c` is
compact. The existing compact-overlap and continuous-history-image
results then make the corresponding overlap and finite-history pieces
compact.
The new explicit interfaces are `prefixTiles_compact_of_window` and
`compact_prefix_historyPiece`. Compactness of a defined history image
does not itself need word fixedness; fixedness and coverage hypotheses
are used when claiming that the family covers the source overlap.

This is a conditional compactness theorem with an explicit geometric
premise. The missing authentic input is to construct the intended stable
space, projection and action from the intended Pisot substitution data,
prove their commutation and closed-embedding properties, and establish
the uniform prefix enclosure (16). In a proper finite-dimensional stable
space a proved uniform norm bound can supply the compact set. Compactness
of the matrix-adic factor does not prove that bound.

An abstract graph-directed attractor is not automatically the same object
as these actual prefix closures. Such an identification needs an
applicable uniqueness argument after both constructions' hypotheses have
been established. Even after authentication and compactness, a complete
finite ancestor constructor, nonunit product-Haar scaling, a valid
overlap-measure recurrence, and strict-root positivity remain separate
requirements. Physical interval length is not compact-overlap measure.

## 8. Controls and executable scope

The mathematical controls below have different roles. The all-erasing
control is implemented in Lean: `erasing_fixedPrefix` and
`erasing_not_cofinalImages` are in `PrefixAddress`, while
`erasing_not_raw_tileEquation` and `erasing_not_prefixTiles_tileEquation`
are in `PrefixClosure`. The latter two apply to arbitrary additive action
and star maps; they use the actual raw origin and the absence of incoming
marks. Their verification receipt remains part of the introducing PR.
The written algebraic and topology counterexamples below are not counted
as additional Lean theorems or native receipts.

| Control | Exact boundary |
| --- | --- |
| Every image empty, `w = 000...` | The four Lean controls above establish the vacuous fixed-prefix condition, failed cofinality, and failure of both raw and closure tile equations. This is the deductive control for the productivity hypothesis. |
| `tau = 1/0/2`, `w = 000...` | The word is fixed at period two, not at period one. With a trivial star map its letter-`0` raw set is nonempty, while the one-step incoming parent set is empty. This is a written period counterexample, not a primitive irreducible Pisot fixture. |
| `tau = 00/1/2`, `w = 000...`, `star(z)=z_0`, `A=0` on `Z` | Without commutation, the raw set is all nonnegative integers but the putative incoming image is only `{0,1}`. This is a written algebraic counterexample. |
| Projection `A(x,y)=(x,0)` of the closed hyperbola `xy=1` | A continuous additive action can send a closed set to a nonclosed set. Closure of its image adds the origin; its image of the closure does not. This is a written topology counterexample to omitting closedness. |
| `sigma = 00/1/2`, `w = 000...`, `E=R`, `B(x)=2x`, `pi(z)=z_0`, actual `H_M` | The closed prefix tile `{(n,iota(n e_0)):n>=0}` satisfies the even/odd equation but is unbounded and noncompact. The other letter tiles are empty. This written example uses an expanding factor, not an intended Pisot stable realization. |
| Repeated letters, repeated parent blocks, coincident projections | Exact records remain distinct even when projected point or residue sets agree. Complete address equality is stronger than support or total-count equality. |
| Truncated output and terminal endpoint | A finite source window certifies exactly its full expansion. A truncation cannot be certified as the whole output, and its terminal boundary is not a selected letter position. |
| Mandatory `00/11/22` inverse-closed forward leak | Each of the two selected sources has four positional pairs: one retained positive pair, one positive exit, and two outside pairs of zero physical calibration. Across both sources the positive-calibration receipt is `full = 4`, `retained = 2`, `positive_exits = 2`. This physical diagnostic remains separate from compact measure. |

The canonical finite contract in
[`kernel/psc/c4_prefix_closure.mojo`](../kernel/psc/c4_prefix_closure.mojo)
binds the original substitution, its block
power, the actual expanded images, a productive prolonging seed, and
complete successive source/output windows. Each target position is tied
to its parent ordinal and local full mark. The source word and parent
ordinal reconstruct the full source mark without changing its meaning.
The bounded constructor limits original image lengths to `3`,
positive block period to `3`, positive transition count to `3`, nonempty
seed length to `32`, each complete
window to `4096` letters, and the aggregate address rows to `12288`.
These are executable resource limits, not mathematical restrictions on
the generic address or closure theorems. No determinant premise is needed
for the finite concatenation/address construction.

The packet binds the full source and target words, the original
substitution exponent, every parent boundary including both endpoints,
and each local before/selected/after split. The integer address rows bind
source-prefix, incidence-transported source-prefix, local-prefix, and
actual global output-prefix Parikh vectors. Thus a changed target word,
truncated target, or overlong target cannot be treated as an equivalent
whole-window certificate. The terminal boundary is retained as a cut,
not mistaken for a selected letter.

| Record | Bound fields |
| --- | --- |
| Local mark | Parent letter, local index, selected letter, prefix and suffix Parikh vectors; the full before and after words are also stored. |
| Occurrence | Parent ordinal, parent letter, mark ID, local index, global output index, selected letter, and the four Parikh triples for source prefix, its `M^k` image, local prefix, and actual output prefix. |
| Cut | Parent ordinal, global output boundary, source-prefix Parikh vector, and expanded-prefix Parikh vector. Both the initial and terminal cuts are present. |
| Whole window | Every letter of the source and target; generation `r` binds `tau^r(U) = sigma^(k*r)(U)` to its complete expansion `tau^(r+1)(U)`. |

The fixed fixtures are `1/021/001` and the reordered `1/012/001` at
period `2`, and `01/02/0` and `00/11/22` at period `1`, each with seed
`[0]` and three transitions. In the named fixture at generation `2`, the
output positions `0` and `29` have distinct parent ordinals `0` and `5`
and the same local position `0`. Their prefix residues at depth `2`
coincide, while the full address records differ. The finite residue
control uses the previously constructed exact image-lattice quotient.

Whole-certificate verification reconstructs all fields, including the
complete literal windows and mark inventory. The lightweight address
lookup is explicitly for a constructed or separately verified
certificate; it does not replace that authentication step.

Independent integer-oracle reconstruction must check literal slices and
prefix identities, rather than trust a native address or infer equality
from a checksum, residue set, or conservation total.
The implemented
[`Python oracle`](../oracles/python/c4_prefix_closure.py) reconstructs
literal expanded prefixes, counts their slices with `Counter`, and locates
each global output position by inverse boundary search. The native
constructor instead enumerates parent/local positions and maintains
streaming prefix counts. The oracle checks the same-residue control with
the existing independent Cramer lattice test. Full packet comparison uses
explicit rejection checks that remain active under `python -O`.

Reproduction entry points are the
[`canonical packet driver`](../kernel/c4_prefix_closure.mojo),
[`native contract tests`](../kernel/tests/test_c4_prefix_closure.mojo),
[`independent tests`](../tests/test_c4_prefix_closure_oracle.py), and the
[`locked replay workflow`](../.github/workflows/c4-prefix-closure.yml).
The workflow binds the PR's exact source head, records source hashes,
executes native tests and the driver, supplies the real packet to the
independent tests, runs the optimized oracle CLI, and rechecks revision
and sources. Its definition is not an assertion that any particular run
has succeeded.

These finite checks support their stated finite premises. They do not
sample-prove the infinite fixed-prefix equation, compact stable bounds,
or complete geometric ancestry. The exact artifact protocol, limits,
source inventory, and observed verification receipts belong to the
introducing pull request and its reproducible driver/oracle artifacts.
