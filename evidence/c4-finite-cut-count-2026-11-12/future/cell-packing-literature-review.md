# Future C4 step: anisotropic fundamental-cell packing

Date: 2026-11-12. **Preimplementation research-design review for a future
increment.** This note is separate from the postimplementation audit of
PR #560 in `count-literature-review.md`. It contains a proposed deductive
argument, not Lean code, a compiled theorem, or an acceptance receipt.

The local interfaces were read at PR #560 source
`31f8046291f2428e839d95e8890c8342858ec210`, tree
`e38c3f65efb79fa72860d8ef222e96695847a551`. Its full isolated verification
was still pending when this review was prepared. `AGENTS.md`, the relevant
append-only side ledger, the earlier count plan/interface review, and the
written matrix-adic bridge were read before investigating this route.

## Decision: GO with a narrower first target

Proceed toward a **finite cell-packing inequality and qualitative positive
Haar measure of the compact represented-pair overlap**, conditional on the
supplied fixed strict carrier and the accepted finite-count interface.
The proposed argument has no apparent mathematical obstruction under the
explicit hypotheses below. The independent model/interface review by
`measure_route` agrees on the fundamental-domain construction and the
quantifier order.

The first implementation need not prove an equidistribution limit, a
regular-window lattice asymptotic, an all-depth residue cardinality formula,
or the exact determinant value of the cell volume. A common positive finite
volume follows instead from equality of measures of fundamental domains
for one countable translation action. The exact numerical normalization
can be a later theorem. No existing written M1 statement is promoted by
this design review.

## Exact space, cells and hypotheses

Use the repository's actual compact inverse limit
`H = MadicResidue.Carrier M`, with its existing compatible-sequence
topology, and a normalized additive Haar measure `ν`. Let

\[
\Phi(x)=(\ell x,\pi x):\mathbb R^3\longrightarrow\mathbb R\times E
\]

be an invertible real linear chart, where `E = Fin 2 → ℝ`. For the named
fixtures, `ℓ = physicalRow` and `π x = W *ᵥ x`; the existing reconstruction
identities supply the inverse. Require the actual integral incidence map
`M` and its real extension to be nonsingular, with `ℓ M = βℓ`, `β>1`,
positive entries of `ℓ`, and contraction of the stable coordinate along
the already proved powers `12*m`.

Set `G = ℝ × (E × H)`, `μ = volume_E.prod ν`, and
`λ = volume_ℝ.prod μ`. The acting group is the original `ℤ³`, by
translation through

\[
\gamma(z)=(\ell z,\pi z,\iota z).
\]

Let `Q` be the **coordinatewise** half-open unit cube and `K_q` the kernel
of evaluation at depth `q`. After the harmless product reassociation, put

\[
F_q=\Phi(M^q Q)\times K_q,\qquad
Q=\prod_{i=0}^2[0,1).
\]

In Lean, `Q` must be `Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)`
or the equivalent `ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))`.
`Set.Ico (0 : Fin 3 → ℝ) 1` uses the product partial order and is a
different set: it includes some upper-face points that the coordinatewise
half-open cube excludes.

**Review correction, 2026-11-12 (`frontier_audit`, confirmed by
`measure_route`):** an initial scratch draft incorrectly called the
product-order interval unbounded and used `(2,0,0)` as its witness. The
interval is bounded; the correct witness is `(1,0,0)`, and the defect is
upper-face nonuniqueness. The statement and control below use the corrected
claim. This correction does not concern PR #560's Lean implementation.

## Proposed proof chain

### 1. The same integer action has each `F_q` as a fundamental domain

Given a point `(r,h) ∈ (ℝ × E) × H`, choose `z₀ ∈ ℤ³` representing
`eval_q h`; this uses quotient surjectivity and `eval_star`. Reduce
`r - Φ(z₀)` modulo the real lattice `Φ(M^q ℤ³)` into its half-open
parallelepiped. If the correcting integer is `k`, use the full diagonal
integer `z = z₀ + M^q k`. The remaining residue lies in `K_q` and the
remaining real point lies in `Φ(M^q Q)`.

For uniqueness, an intersection of two translated cells first forces
`z-z' ∈ M^q ℤ³` by the residue coordinates. In the same residue coset,
the half-open real parallelepiped has a unique lattice representative.
Thus distinct integer translates are disjoint. Measurability follows from
the invertible real chart, coordinatewise half-open cube and clopen kernel.
This proves an exact partition, although the later finite packing step
only needs its measurable, pairwise-disjoint part.

The construction needs neither density of the internal projection nor
injectivity of the physical projection alone. It uses the injective full
real chart and the matching matrix power in both coordinates.

### 2. Obtain a fixed positive finite cell mass without a determinant calculation

All `F_q` are fundamental domains for the same countable additive action,
which preserves `λ`. Hence `λ(F_q)=λ(F_0)` by fundamental-domain measure
equality. Write this common real value as `c` after proving it finite.

At depth zero, `K_0=H`. The set `F_0` contains a nonempty open set and
has compact closure. The product Haar measure therefore gives
`0 < λ(F_0) < ∞`. This proves `0<c<∞` without identifying `c` with a
particular determinant or with the repository's already named `kappa`.

The familiar calculation
`|det Φ| * |det M|^q * ν(K_q) = |det Φ|` is consistent with this
construction, but it is not an available identity merely from the names.
An exact formula requires the chosen coordinate Haar normalization and the
all-depth index computation. They may be deferred for qualitative positivity.

### 3. The internal cell width tends to zero along the block powers

The internal projection of `F_q` is
`W_q = π(M^q Q) × K_q`. The closed unit cube has a uniform stable-image
bound. The existing stable block contraction makes its image under
`M^(12*m)` tend uniformly to zero. Compatibility makes the kernels
decrease, and the existing neighborhood-basis theorem makes them cofinal
among zero neighborhoods. Consequently, for every zero neighborhood `V`
in `E × H`, some fixed `q=12*m` has `W_q ⊆ V`.

The physical coordinate of `F_q` is contained in `[0,L_q]`, for example
with `L_q=β^q * ∑ i, ℓ i`. The exact endpoint value is unimportant here;
finiteness and a valid upper bound suffice. It need not tend to zero.

### 4. Finite packing, directly into a measurable containing rectangle

Let `Z ⊂ ℤ³` be finite, with `0 ≤ ℓ z < X` and internal image in `U`.
If `U + W_q ⊆ O`, where `O` is an open set of finite `μ` measure, then

\[
\bigsqcup_{z\in Z}(\gamma(z)+F_q)
\ \subseteq\ [0,X+L_q]\times O,
\qquad
c\,\#Z\le (X+L_q)\,\mu(O).
\]

Finite additivity on the disjoint measurable cells, translation invariance,
product measure and monotonicity give the inequality. There is no need to
assert that the Minkowski sum `U+W_q` is measurable, to calculate its
measure, or to count every lattice point in the rectangle. The input is
already the finite set of original integer cuts.

### 5. Contradict zero measure of the compact carrier overlap

Fix a strict carrier `C`, source `T ∈ C`, and a positive uniform factor
bound `L`. Positivity of `L` follows from a nonempty top word and the
positive physical row. Let `I = carrierOverlap fixture C`; it is compact.
Assume `μ(I)=0`. Outer regularity gives an open `O ⊇ I` with
`μ(O) < c/(2L)`. Compactness and continuity of addition give an open zero
neighborhood `V` with `I+V+V ⊆ O`.

Choose `q=12*m` once so `W_q ⊆ V`. The existing compact-open capture
applied to the fixed open set `I+V` places all later counted cuts there.
The PR #560 inequality gives `X_n ≤ L * #Z_n`, while
`X_n=β^(12*n) * physicalLength physicalRow T.1` tends to infinity.
For a sufficiently late `n`, also `X_n > L_q`. The packing inequality
would then imply

\[
\frac{cX_n}{L}\le c\,\# Z_n
\le (X_n+L_q)\mu(O)
<\frac{cX_n}{L},
\]

a contradiction. This proves the proposed qualitative conclusion
`0 < μ(I)`. The order is **choose `O`, then `V`, then fixed `q`, then
let `n` grow**. No limit exchanges or moving-depth count estimate are used.

## Five primary sources checked

1. **Minervino–Thuswaldner, closest nonunit construction:**
   [The geometry of non-unit Pisot substitutions](https://arxiv.org/pdf/1402.2002),
   Lemmas 3.5–3.6. Their full arithmetic representation has a lattice and
   an explicit real/finite-place fundamental domain. This is relevant
   precedent, not an identification with this compact matrix-adic carrier.
   The proposed partition is proved directly for the original integers.

2. **Mathlib, strongest directly reusable measure statement:**
   [FundamentalDomain](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/FundamentalDomain.html),
   `IsAddFundamentalDomain.mk'` and `IsAddFundamentalDomain.measure_eq`.
   A measurable unique orbit representative constructs a fundamental
   domain. Equality of domain measures requires a countable acting group
   and measurable, measure-preserving translations. This is the precise
   route to constant cell mass, not a model-set frequency theorem.

3. **Mathlib, half-open parallelepipeds and floor reduction:**
   [ZLattice.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/ZLattice/Basic.html),
   `ZSpan.fundamentalDomain_pi_basisFun`, `map_fundamentalDomain`,
   `exist_unique_vadd_mem_fundamentalDomain`,
   `fundamentalDomain_measurableSet`, and `isAddFundamentalDomain`.
   These formalize coordinatewise half-open cells, their linear transports
   and uniqueness of the integer reduction. The measure and determinant
   lemmas are available if a later exact normalization is desired.

4. **Mathlib, Haar hypotheses and normalization:**
   [Haar.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Haar/Basic.html),
   `addHaarMeasure_self`, `regular_addHaarMeasure` and
   `isAddHaarMeasure_addHaarMeasure`. Haar measure is translation invariant,
   finite on compact sets and positive on nonempty open sets. A specified
   positive compact set fixes its normalization. The full compact carrier
   can be normalized to mass one; a noncompact finite-place field cannot
   simply be substituted with this normalization.

5. **Mathlib, small open supersets of compact null sets:**
   [Regular](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html),
   `Set.exists_isOpen_lt_of_lt` and
   `IsCompact.exists_isOpen_lt_of_lt`. These provide the required open
   cover under their outer-regular or compact-inner-regular/local-finiteness
   assumptions. No null-boundary hypothesis on `I` is needed. The product
   measure's actual regularity instance must still be supplied rather than
   assumed from a symbol named Haar.

The key fundamental-domain and regularity declarations were also found in
the available source cache corresponding to the project's pinned Mathlib
revision. This was a read-only API check, not a compilation experiment.

## Existing bindings and still-needed interfaces

| Role | Existing repository material | Future proof obligation |
|---|---|---|
| Exact matrix-adic arithmetic | `MadicResidue.quotient_surjective`, `quotient_eq_iff`, `eval_star`, `eval_surjective`, `reduction_eval` | Bind real cell reduction to the same integer residue and prove the unique full representative. |
| Compact carrier and Borel structure | `MadicResidue.carrier_compactSpace`, `MadicHaar` instances | Instantiate normalized Haar and product invariance/regularity with the actual model. |
| Full physical/stable chart | `NamedStableChart.reconstruction`, `physical_L`, `W_L`, `MZ_det` | Package the actual chart as a continuous linear equivalence; avoid a stable projection standing in for it. |
| Shrinking widths | `NamedStableChart.W_MR_pow`, `NamedCutProximity.block_contract`, `CompactNeighborhood.exists_zeroSlice_subset` | Uniformly bound the closed cube and combine stable contraction with a cofinal kernel depth. |
| Uniform tube around a compact set | `CompactNeighborhood.eventually_translate_mem` | Choose open `V` with `I+V+V ⊆ O`. |
| Actual cuts | PR #560's `integerStarts_count_and_strip` and `eventually_integerStarts_mem`; PR #558's `carrierOverlap_compact` | After acceptance, compose them with the finite packing theorem and prove the elementary growth/positive-bound adapters. |

## Required control boundaries for later implementation

- **Coordinate cube:** `(1,0,0)` belongs to the product-order interval
  `Ico 0 1` but not the coordinatewise unit cube. This face point and the
  zero vector differ by an integer vector, destroying the exact unique
  representative claim. The product-order interval remains bounded.
- **Half-open faces:** closed cells have shared boundary representatives;
  exact uniqueness requires half-open coordinates. An almost-everywhere
  version would need the corresponding null-boundary argument explicitly.
- **The residue factor matters:** in the one-dimensional `M=2` model,
  `[0,2) × H` and its diagonal translate by one overlap. The matching
  `ker(eval_1)` separates the two residue classes. This is an abstract
  normalization/control example, not a standing-Pisot counterexample.
- **Depth is fixed before growth:** if a chosen physical cell width grows
  faster than `X_n`, the boundary term need not disappear. There is no
  warrant for choosing `q` from `n` and silently using a fixed-depth limit.
- **Mass and invertibility are real obligations:** a singular real chart
  can give zero-volume cells; matching domain names does not supply a
  positive constant. Haar normalization must be the same at every depth.
- **Only the stated internal compact set is targeted:** capture is uniform
  over the fixed represented-pair carrier, not an infinite moving family.
  No per-pair frequency, Euclidean projection of a null set, degree-one
  tiling, strong-coincidence converse, or general C4/PSC conclusion follows.

This is standard fundamental-cell geometry and finite measure packing,
specialized to a useful anisotropic family. Its contribution would be the
exact original-integer/matrix-adic binding and composition with the literal
cut theorems. No new executable mathematical algorithm or census is needed.
Commit a scoped pre-code gate before any implementation; keep this future
route separate from the current PR's verification and its historical evidence.
