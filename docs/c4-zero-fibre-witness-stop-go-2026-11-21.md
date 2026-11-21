# Zero-fibre witnesses: source decision before formal development

## Proposed claims and scope

Continue from PR #643, exact head
`7a5025ed7b8104413477ea7fbd15b52206e0959c`, for the literal
`sigma_k = (1, 0 1^k 2, 001)`. The desired missing statement is that,
for every `k >= 2` and every pair `T,U` over the zero solenoid history,
there are legal hull members `T',U'` and one real `t` satisfying

1. `Agree 1 T T'`;
2. `Agree 1 U U'`;
3. `Agree 1 (translate t T') (translate t U')`.

The existing consumer is
`Psc.ParameterFamilySolenoid.common_tile_of_zero_fibre_witnesses`.
It derives periodicity from the already proved finite zero fibre and
uses `Psc.ParameterFamilyTiling.periodic_common_tile_of_origin_witnesses`.
The latter needs only three equalities of **closed** origin patches.
The proposed work investigates the relationship between these exact
interfaces, preserves seam tiles, and derives any post-witness
consequences that need no new geometric hypotheses.

A separate negative control tests the stronger assertion that the
original pair itself has equal closed origin patches, or `Agree 1 T U`.
That stronger assertion is not the intended witness statement.

## Primary sources checked

1. Barge, Stimac and Williams, *Pure discrete spectrum in substitution
   tiling spaces*, DCDS 33 (2013), 579--597,
   [DOI](https://doi.org/10.3934/dcds.2013.33.579),
   [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf).
   The global assumptions in Section 2 are primitivity, aperiodicity and
   finite local complexity. Theorem 2.3 gives the finite-to-one solenoid
   factor for Pisot family tilings. Corollary 1 identifies equality under
   the **maximal** equicontinuous factor with strong regional proximality.
   Theorem 3.1 uses the three closed-origin agreements for periodic
   partners and the transfer from legal patches sharing a tile. This is
   the closest existing construction; the repository already formalizes
   the latter transfer.

2. Barge and Kellendonk, *Proximality and pure point spectrum for tiling
   dynamical systems*, Michigan Math. J. 62 (2013), 793--822,
   [DOI](https://doi.org/10.1307/mmj/1387226166),
   [author preprint](https://arxiv.org/pdf/1108.4065).
   In the inspected preprint, Theorem 3.4 proves that regional proximality
   is strong regional proximality for repetitive Meyer tilings. The
   geometric argument removes a residual small translation because its
   possible values lie in a fixed uniformly discrete combination of
   puncture sets. Ordinary topological approximation alone does not
   remove this translation. Lemma 5.12 supplies the surrounding
   substitution/proximality context. Expanding a shared tile in a pair
   fixed by a common power of inflation gives arbitrarily large shared
   patches; this elementary local step can be formalized directly.

3. Baker, Barge and Kwapisz, *Geometric realization and coincidence for
   reducible non-unimodular Pisot tiling spaces with an application to
   beta-shifts*, Ann. Inst. Fourier 56 (2006), 2213--2248,
   [DOI](https://doi.org/10.5802/aif.2238),
   [published PDF](https://www.numdam.org/item/AIF_2006__56_7_2213_0.pdf).
   Section 3 constructs the nonunit inverse-limit realization. Theorem
   4.2 relates coincidence rank to generic fibre cardinality. These
   conclusions concern the specified geometric realization, not an
   arbitrary finite-to-one factor. The target identification and
   invariant-measure conclusions cannot be replaced by the already
   compiled finite-fibre theorem.

## Hypotheses that transfer and boundaries

PR #643 already provides the literal positive Perron geometry,
recognizability, continuous onto solenoid realization, translation and
inflation equivariance, finite fibres, and zero-fibre periodicity.
The ordinary hull and its aperiodicity/finite local complexity are
earlier family results. These are available for continued formal work.

The identification with the published maximal equicontinuous factor is
still a written correspondence. Neither its universal property nor a
regional-proximality theorem is presently a Lean theorem for this map.
Consequently one cannot apply Corollary 1 inside Lean just by renaming
the existing map. The Meyer exactification step is a further geometric
argument if that route is chosen. No new field called “maximal” or
“same-fibre witnesses” will be treated as discharged evidence.

There is also a useful shorter downstream interface: for an
inflation-periodic pair, a shared tile expands to exact agreement on
arbitrarily large windows after a common translation. This uses only
positive lengths, strict expansion, and the existing inflation/tiling
laws. It does not establish the missing shared tile from equal images.

## Negative controls

The literal seam tiling furnished by `fixed_hull_tiling` has a tile of
type `1` beginning at zero and is fixed by squared inflation. Its image
under one inflation has a tile of type `0` beginning at zero, since
`sigma_k(1)` begins in `0`. Both realize to zero, by `realize_r4` and
inflation equivariance. A tiling cannot contain these two different
tiles at the same start. Therefore equal zero histories do not imply
equal original closed-origin patches or direct radius-one agreement.
This control holds for every `k >= 1`; it does not refute the required
three-agreement existential statement.

For `k >= 2`, this same pair also gives a positive literal control. The
right ray of `T` begins `101`, while that of its inflation begins `011`.
The third tiles are both type `1` and start at `ell(0) + ell(1)` because
the preceding words `10` and `01` have the same length. Expanding this
common tile through the common period gives genuine exact common-shift
witnesses at every requested radius. This settles one explicitly
constructed pair, not every pair in the zero fibre.

A second literal control investigates the tempting restriction to
origin-vertex tilings. The proposed singleton seed is the type-`1` tile
starting at `-ell(0)`. Its three successive origin-tile starts are
`-ell(0)`, `ell(0)-ell(1)`, `-ell(2)`, and `-ell(0)` again. The selected
prefixes are `0`, `0 1^(k-1)`, and `01`. The length eigenvector identities
verify this cycle for every `k >= 2`. All three tiles contain zero in
their interiors. The existing growing-seed theorem may therefore
construct a legal tiling fixed by cubed inflation. A separate exact
realization calculation must still establish that this interior cycle
is in the zero fibre; periodicity alone is not enough. Proceed with
these two stages separately and do not use “zero implies vertex” as an
assumption.

As a separate abstract warning, finite fibres, onto continuity, minimal
translation dynamics and an invertible expanding inflation alone do not
identify the maximal equicontinuous factor. On the dyadic solenoid,
multiplication by three is a finite-to-one factor commuting with the
shift; rescale the source flow to preserve the same real time parameter.
Its nonzero order-three kernel points are periodic under the shift,
whereas an equicontinuous action has diagonal regional proximality.
This is a counterexample to an abstract implication from that factor
package, not a counterexample to the literal substitution family.

## Decision

An additional bounded exploratory check may test the proposed shortcut
“zero history forces an origin vertex.” For a strictly internal occurrence
of letter `a` in `sigma_k^n(a)`, let `p` be its exact prefix-count vector.
The affine fixed-point equation is `(M^n - I)v = p`; integrality of `v`
is a candidate for zero realization of an interior periodic tiling.
Enumerate only explicitly stated parameters, depths and word-size budgets,
using rational matrix arithmetic and literal words. Such a search is a
counterexample generator, not a universal classification or a proof of
the correspondence with the realization. Any successful candidate still
requires that correspondence to be checked before promotion.

The exploratory check used `k=1,2,3,4,5`, depths `1` through `6`, and
a maximum expanded-word length of `10^6`. It found the integer candidates
`e0`, `e1-e0`, and `e2` at period three for `k=2,3,4,5`. These are
discovery observations, not an archived replayed finite certificate or
an exhaustive classification. The final uniform Lean construction in
`C4ParameterFamilyInteriorSeed.lean` and full-history verification in
`C4ParameterFamilyInteriorZero.lean` supersede that exploratory evidence.
The next deductive target is uniform:
construct a literal legal tiling fixed by cubed inflation with its type-1
origin tile starting at `-ell(0)`. The existing nested-seed construction
and three explicit child placements give this target. Independently,
the stable-series formula proves that an inflation-periodic tiling whose
origin start is the negative length of an integer vector realizes to
zero: along period multiples its integer partial sums converge after
adding a vanishing stable projection. The converse follows from the
integer torus lift and `dot_realVec`. This characterization reuses the
constructed map and introduces no maximal-factor premise. Once checked,
it would refute the proposed origin-vertex shortcut using an actual
member of the literal zero fibre, rather than only an affine candidate.

Proceed with the literal zero-fibre control, exact comparison of the
witness interfaces, and expansion of a shared tile into arbitrarily
large exact common-shift windows. Continue investigating the missing
geometric implication, but preserve it as an explicit unresolved
obligation unless it is proved from the existing construction. Do not
promote coincidence rank one or the invariant-measure `L²` conclusion
from the finite-fibre theorem alone. This work is a local review
candidate; publication and merging require separate user approval.

## Follow-up local claim: the period-three interior orbit

Continue with a literal local coincidence calculation, without an
exhaustion claim for the zero fibre. For every `k >= 2`, suppose `T` is
fixed by squared inflation and contains `(1,0)`, and `U` is fixed by
cubed inflation and contains `(1,-length(0))`. The proposed common tile
is of type `0` at `length(1) + beta*length(1)`.

The calculation uses only the first two occurrences of `1` in
`sigma_k(1)` and `beta*length(0)=length(1)`. On the seam side, the second
`1` after one inflation begins at `length(0)+length(1)`; its first
child after another inflation is the claimed `0`. On the interior
side, the second `1` after one inflation begins at `length(0)`.
Its first `1` child after another inflation and then its first `0`
child after a third inflation produce the same coordinate. The stated
periods return both tilings. This is the same standard local expansion
mechanism as the preceding source decision, specialized to literal
words. Proceed with an exact Lean calculation and the common-window
consequence. Do not infer that every zero-fibre tiling belongs to this
orbit or to the seam orbits.
