# Read-only review: anisotropic cells for a finite cut upper bound

2026-11-12. Repository interfaces inspected at PR #560 commit
`31f8046291f2428e839d95e8890c8342858ec210`, tree
`e38c3f65efb79fa72860d8ef222e96695847a551`; pinned Mathlib APIs were read
from the existing package source cache. No theorem code, tests, builds,
repository changes, or new acceptance claims were made. PR #560's required
gate was running during this review.

## Assessment

**The proposed packing route is mathematically sound under the stated
actual-model hypotheses.** It can prove the qualitative positive-overlap
conclusion needed to contradict nullity without a full equidistribution
theorem, a boundary-null window, or a count of every point in a model set.
The new fundamental-cell and measure lemmas remain substantial explicit
proof obligations; none is supplied merely by this assessment.

Recommended first target: finite packing plus qualitative positivity of
the compact represented-pair overlap. Take the common cell mass as an
unspecified positive finite constant. Identifying it with `kappa`, and
proving an all-depth quotient-cardinality formula, can be deferred.

The parallel primary-source review is
`count-cell-packing-literature-review.md`. Its narrowed design agrees with
this audit; a committed pre-code decision is still required before a new
implementation.

## 1. The exact space and cells

Let `M` be the original integer incidence endomorphism, `A` its real
extension, `H = MadicResidue.Carrier M`, and `η = MadicResidue.star M`.
Use the actual invertible physical/stable chart

\[
 \Phi(x)=(\ell x,Wx):\mathbb R^3\longrightarrow\mathbb R\times E,
 \qquad E=\operatorname{Stable}.
\]

Put `μ = volume_E.prod ν` for the same normalized Haar measure `ν` used
by the named overlap theorems, and `λ = volume_ℝ.prod μ`. The full group
is `ℝ × (E × H)`, and the integer translation is

\[
 \gamma(z)=(\ell z,Wz,\eta z).
\]

This full translation is injective because `Φ` is injective on the real
coordinates. Neither `η` nor the internal map `z ↦ (Wz,ηz)` needs a
separate injectivity assumption.

Define, with the natural product reassociation,

\[
 Q=\prod_{i=0}^2[0,1),\qquad
 K_q=\ker(\operatorname{eval}_q),\qquad
 F_q=\Phi(A^q Q)\times K_q.
\]

**Keep the joint real parallelepiped.** Its physical and stable coordinates
are correlated. It is legitimate to multiply its joint real measure by
`ν(K_q)`; it is not legitimate to replace it by the product of its two
real projections when calculating its mass. A rectangular enclosure is
used only for the eventual upper bound.

In Lean the cube is `Set.pi Set.univ (fun _ : Fin 3 => Set.Ico (0 : ℝ) 1)`.
`ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))` is equivalent. The
product-order interval `Set.Ico (0 : Fin 3 → ℝ) 1` is different: it
includes an upper-face point such as `(1,0,0)`. It is bounded, but would
lose exact uniqueness on those faces. Closed cubes have the same exact
disjointness problem; an almost-everywhere variant would need its own
null-boundary argument.

## 2. Exact partition by the same integer action

**Disjointness.** Suppose a point belongs to `γ(z)+F_q` and `γ(w)+F_q`.
Applying `eval_q` to its carrier coordinate gives equal residues for
`z,w`. Existing `quotient_eq_iff` gives `z-w=M^q k` for an actual integer
`k`. Equality of the joint real coordinates, compatibility of the real
extension, and invertibility of `A^q` then give `k=v-u` for two vectors
`u,v∈Q`. Every coordinate of this integer vector lies strictly between
`-1` and `1`, hence is zero. Therefore `z=w`.

**Coverage.** Given `(r,h)∈(ℝ×E)×H`, choose an integer representative
`z₀` of `eval_q h`. Let `a=A^{-q}(Φ^{-1}(r)-z₀)`. Write
`a=k+u` by coordinatewise floor, with `k∈ℤ³` and `u∈Q`. Set
`z=z₀+M^q k`. The remaining real coordinate is `Φ(A^q u)` and the
remaining carrier coordinate is in `K_q`. Thus the point lies in `γ(z)+F_q`.
For `IsAddFundamentalDomain.mk'`, whose convention asks for
`g +ᵥ x ∈ F_q`, use the negative of this translation index.

Both parts use the same original `M^q` in the quotient and the real
parallelepiped. They do not replace `H_M` by `H_(M^q)` or by a finite-place
field. `eval_star`, quotient surjectivity, and the image-lattice equality
are exactly the required arithmetic; density of an internal projection
is unnecessary.

The cell is Borel: the real map is a homeomorphism, the coordinate cube
is Borel, and `K_q` is clopen by continuous evaluation into a discrete
quotient. The proof must instantiate the actual Borel/product topology
facts; arbitrary images of measurable sets are not being used.

## 3. A common positive mass without computing a determinant

There are two valid paths to a common mass.

**Recommended qualitative path.** Regard every `F_q` as an exact measurable
fundamental domain for the same countable group `ℤ³` acting through `γ`.
Translations preserve `λ`. Mathlib's
`MeasureTheory.IsAddFundamentalDomain.measure_eq` gives

\[
 \lambda(F_q)=\lambda(F_0).
\]

This use of `measure_eq` needs coverage as well as disjointness. Although
finite packing alone only needs disjointness and a known cell mass, the
recommended derivation of that mass must not omit the coverage proof.

At level zero, `K_0=H`. The real base cell contains the image of `(0,1)^3`
and is contained in the image of `[0,1]^3`. Consequently `F_0` has nonempty
interior and compact closure. Product Haar positivity and local finiteness
give `0<λ(F_0)<∞`. Define the real constant `c=λ(F_0).toReal` only after
these facts, so `c>0` and `λ(F_q)=ENNReal.ofReal c`.

**Optional exact normalization path.** A separately proved Jacobian and
kernel-index formula give

\[
 \lambda(F_q)=|\det\Phi|\,|\det M|^q\,\nu(K_q)=|\det\Phi|.
\]

For the named chart, the packed three-row matrix has rows `physicalRow`,
`W 0`, and `W 1`. Its determinant algebraically equals
`-(a + beta + b * NamedStableChart.c) = -kappa`, using
`physical_r_eq_kappa`; the chart coefficient here is distinct from the
cell-mass constant `c`. This calculation is
not yet a compiled Jacobian/covolume binding. The real product-measure
coordinate identification and `ν(K_q)=2^(-q)` also need proofs if this
normalization is claimed. Existing `first_residue_card` and
`measure_first_kernel` only state depth-one formulas.

The full group with its compact matrix-adic factor is not a real vector
space, so `ZLattice.covolume` for a real normed vector space cannot simply
be applied to it. The general fundamental-domain measure API is the
appropriate first interface. A positive finite `c` suffices for nullity
contradiction and imposes no hidden normalization assumption.

## 4. Uniform internal shrinking and a finite physical extent

Let the internal projection of the cell be
`W_q = (W ∘ A^q) '' Q × K_q`. For the named matrix,
`W_MR_pow` and `B_pow_apply_eq_matrix` identify the stable action exactly.
`NamedCutProximity.block_contract` gives

\[
 \|B^{12r}y\|\le (7/8)^r\|y\|.
\]

A finite bound `D` on `‖Wv‖` for `v∈[0,1]^3` is enough. One can even
take `D=beta`: `W_mulVec`, `a_pos`, `b_pos`, and
`a_add_b_add_one` bound both absolute coordinate row sums by `beta`.
The bound itself still needs a small proof; no optimized constant is needed.

Given a zero-neighborhood `V` in `E×H`, existing
`CompactNeighborhood.exists_zeroSlice_subset` provides `ε>0` and depth `m`.
Choose `r` so `(7/8)^r D<ε` and `m≤12r`. Compatibility
`reduction_eval` makes `K_(12r)⊆K_m`. Hence `W_(12r)⊆V`.
Only this subsequence of cell depths is needed; no new all-exponent
contraction estimate is required.

The positive physical row and `physical_eigen` give

\[
 0\le \ell(A^qv)\le L_q,
 \qquad L_q=\beta^q\sum_i\ell_i<\infty.
\]

`L_q` may be very large. This is harmless only because `q` will be fixed
before the cut-generation parameter tends to infinity. Physical/stable
intertwining and real/integer power compatibility must bind to the same
literal incidence matrix; equal names alone do not supply that binding.

## 5. The finite packing inequality

The elementary next measure lemma can be stated for a finite
`Z : Finset (Fin 3 → ℤ)`. Assume

- `0≤ℓz<X` and `star z∈U` for every `z∈Z`;
- `F_q⊆[0,L_q]×W_q` and `U+W_q⊆O`;
- `O` is measurable, with finite `μ` measure, and `X≥0`, `L_q≥0`;
- the cells are measurable, pairwise disjoint under distinct integer
  translations, and have the common positive finite mass `c`.

Then

\[
 \bigcup_{z\in Z}(\gamma(z)+F_q)
 \subseteq [0,X+L_q]\times O,
 \qquad c\,\#Z\le (X+L_q)\mu(O).
\]

Use finite additivity, translation invariance, product measure and
monotonicity. Mathlib has `measure_biUnion_finset` and its null-measurable
version `measure_biUnion_finset₀`, plus `Measure.prod_prod` and
`Real.volume_Icc`. The initial statement may use `ℝ≥0∞` throughout;
conversion to real arithmetic must retain the established finiteness.

There is **no need to measure `U+W_q`**. It is only an inclusion premise.
There is also **no need to prove finiteness of all integer points** in the
strip/window, since PR #560 already supplies the finite input `Z_n`.
The upper bound is on each supplied finite set of original integers, not
on an ambient image or a set of auxiliary prefix witnesses.

## 6. The nullity contradiction and quantifier order

Let `I=carrierOverlap fixture C` for a fixed supplied strict carrier.
Choose `T∈C` and a finite positive carrier factor bound `L`. Any valid
positive upper bound suffices; an attained maximum is not necessary.
The source top word is nonempty, so its positive physical length and
`beta>2` give
`X_n=beta^(12*n)*physicalLength physicalRow T.1 → ∞`.

Assume `μ(I)=0`. Regularity gives an open `O⊇I` with
`μ(O)<c/(2L)`. Compact uniform translation and continuity of addition give
an open zero-neighborhood `V` with `I+V+V⊆O`. The sum `I+V` is open and
contains `I`; no measure assertion about that sum is required.

Choose `q=12r` once with `W_q⊆V`. PR #558/PR #560 capture then gives one
threshold for `star '' Z_n ⊆ I+V`. Choose a later `n` with `X_n≥L_q`.
The proposed packing bound and PR #560's finite lower bound would give

\[
 \frac{cX_n}{L}\le c\,\#Z_n
 \le (X_n+L_q)\mu(O)
 \le 2X_n\mu(O)
 <\frac{cX_n}{L},
\]

a contradiction. This establishes the proposed qualitative conclusion
`0<μ(I)` once the new lemmas are proved. Empty `I` is also covered by
the contradiction; no nonemptiness premise was silently introduced.

The order is **fixed carrier/source and bound; then `O`; then `V`; then
fixed cell depth `q`; then capture threshold and sufficiently large `n`**.
Choosing `q` from `n` would require an additional relative-growth argument
and is not licensed by this proof. The physical growth step is elementary,
but still needs a Lean adapter from the existing positive-row/root facts.

## 7. Existing APIs and minimal next obligations

| Role | Verified existing declarations | Proposed missing binding |
| --- | --- | --- |
| Original residues | `quotient_surjective`, `quotient_eq_iff`, `eval_star`, `eval_surjective`, `reduction_eval` in `MadicResidue` | Match real cell differences and floor corrections to the exact integer power range. |
| Carrier topology | `carrier_compactSpace`, `continuous_eval`; `MadicHaar` Borel instances | Install actual product measurability, invariant measure, and regularity instances. |
| Real chart | `reconstruction`, `W_L`, `physical_L`, `physical_r_eq_kappa`, `kappa_pos` in `NamedStableChart` | Package `Φ` as a continuous linear equivalence with inverse `L y+(t/kappa)•r`. |
| Named action | `MZ_det`, `castZ_mulVec`, `physical_eigen`, `W_MR_pow`, `B_pow_apply_eq_matrix`; named `incidence_eq` | Power compatibility of the chosen real map with original `M`. |
| Fundamental domains | `IsAddFundamentalDomain.mk'`, `.measure_eq`; `ZSpan` floor/fundamental-domain APIs | Define the diagonal action and cells; prove Borel unique representatives and common positive finite mass. |
| Shrinking widths | `NamedCutProximity.block_contract`, `exists_zeroSlice_subset` | Uniform cube bound and cofinal block-depth cell containment. |
| Packing | `measure_biUnion_finset`, product measure and interval volume | Finite translated-cell enclosure and the upper inequality. |
| Small neighborhoods | `CompactNeighborhood.eventually_translate_mem`; `Set.exists_isOpen_lt_of_lt`, `IsCompact.exists_isOpen_lt_of_lt` | Open `V` with `I+V+V⊆O`; verify actual regularity/local finiteness hypotheses. |
| Actual cuts | `integerStarts_count_and_strip`, `eventually_integerStarts_mem`, `carrierOverlap_compact` | Positive bound/source length, growth, and the finite contradiction. PR #560 acceptance remains separately required. |

Mathlib's `IsAddFundamentalDomain.measure_eq` requires the **same countable
action**, `MeasurableConstVAdd`, and `VAddInvariantMeasure`. The actual
translation action supplies these through additive Haar invariance; they
must be instantiated. For regularity, the existing finite discrete quotient
and compact-carrier construction supports a metrizable, sigma-compact
product, and `Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` is
available. This is an API path, not an already checked instance proof.

A practical new increment can separate (1) diagonal cells and common mass,
(2) named chart/width binding plus finite packing, and (3) the compact-null
contradiction. Stabilize shared definitions first. Do not mix a determinant
normalization project or an all-model-set asymptotic into this first target.

For later nullity assembly, `ArchivedPayloadConsumer.Packet.roots_null`
is conditional on an actual valid accepted payload. `archivedRoot` lists
the three zero-offset unordered pairs; `OccurrencePiece.overlap` at zero
is exactly the corresponding tile intersection. A finite-pair/symmetry
adapter can therefore make all represented distinct-pair intersections
null once that payload is bound. This uses roots only and does not require
identifying the archived domain with all strict packets. Neither the
payload binding nor the final positivity/nullity combination is supplied
by this route note.

## Controls to retain in the next gate

Use the wrong product-order half-open interval to expose a duplicated
boundary representative; omit the residue kernel in the one-dimensional
`M=2` model to expose overlapping cells from different residue classes;
use a singular real chart to expose zero-volume cells; and let the cell
depth grow with the cut scale to show that the boundary term need not
vanish. Retain the distinction between the joint real cell and the product
of its projections. These are controls for the construction, not Pisot
counterexamples. No code or tests for them were written here.

The route avoids a full equidistribution theorem at the qualitative scope
reviewed above. It does not by itself certify the written numerical M1
constant, any concrete payload, general C4, or PSC.
