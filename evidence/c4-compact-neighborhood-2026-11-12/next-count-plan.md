# Next counting obligation after compact-neighborhood transfer

Read-only audit, 2026-11-12. Checkout:
`/workspace/scratch/f96c28a561ad/psc-compact`, committed HEAD at inspection
`571c8df9b5223aeef6b7f137c49b4495590d090e`, based on main
`bdf033f647f73f911a47260e8bdad5f2e96f3c7a`. The new neighborhood modules were
also inspected as worktree sources; this plan does not certify their final
acceptance. No new theorem code, executable computation, or premise was added.

## Recommendation: count the literal integer cuts first

The smallest substantive next Lean target is an exact finite lower bound on
the number of **original common Parikh cut vectors**, obtained from the
existing complete reduction. The fixed-origin regular-cylinder lattice
estimate is a separate, substantially larger analytic obligation.

For a supplied `StrictSystem s C`, source `T ∈ C`, and exponent `k`, put
`u_k = (subst s)^[k] T.1`, `v_k = (subst s)^[k] T.2`, and
`bs = red u_k v_k`. Define a finite set `Z_k ⊆ (Fin 3 → ℤ)` of the
common Parikh vectors at actual proper balanced cuts of `(u_k,v_k)`.
Use literal top positions/full marks, with an actual bottom mark witnessing
balance. Include the cut at zero and exclude the terminal endpoint.

For a positive physical length row `ℓ`, let
`L_max = max_{U ∈ C} physicalLength ℓ U.1`. The finite nonempty strict
carrier and nonempty state words make this maximum positive. The proposed
finite theorem is

\[
\operatorname{physicalLength}_\ell(u_k)
\le L_{\max}\,\#Z_k.
\]

Its proof has four concrete parts:

1. Every member of the complete ordered list `bs` lies in `C` and is a
   nonempty balanced block. Its top physical length is at most `L_max`.
2. The top and bottom prefixes preceding each factor are balanced.
   The factor's first letters give two genuine full marks in `u_k,v_k`.
   Strictness makes their labels distinct and represented by `CutPair C`.
3. Different factor ordinals yield different original Parikh vectors:
   their top prefix lengths strictly increase. Equality of Parikh vectors
   would imply equal word lengths. Repeated factor *labels* therefore do
   not collapse factor *occurrences*.
4. `red_top`, physical additivity and the bound on each factor give
   `physicalLength ℓ u_k ≤ L_max * bs.length ≤ L_max * Z_k.card`.

For the named fixtures, take `ℓ = physicalRow` and `k = 12*n`. Existing exact
substitution scaling gives

\[
X_n=\beta^{12n}\operatorname{physicalLength}_\ell(T.1),\qquad
X_n\le L_{\max}\#Z_{12n},\qquad
0\le\ell z<X_n\quad(z\in Z_{12n}).
\]

No Perron frequency limit or SCC-period argument is needed for this total
cut bound. The positive source length and `beta_gt_two` also give
`X_n → ∞`. Per-pair frequency bounds are a different, stronger task.

Each `z ∈ Z_{12n}` maps into the new `NamedCutNeighborhood.cutPoints`.
For an open `U` covering the represented cut-pair overlaps, the new
`eventually_carrierOverlap_strict_cuts_mem` adapter then gives
`star '' Z_{12n} ⊆ U`.
**Keep the cardinality on `Z_{12n}`.** `cutPoints` is a set in the internal
product, and its cardinality is not a substitute without an additional
injectivity proof. The auxiliary anchored reference ordinals are also
not known to be injective and must never be counted instead.

## Exact reusable sources and remaining finite work

Paths below are relative to `proof/PscVerif/PscVerif/`.

| Input | Existing declarations and exact boundary |
| --- | --- |
| Full factorization and closure | `Reduction.lean`: `red_top`, `red_bot`, `red_ne_nil`; `StrictSystem.lean`: `StrictSystem.mem_of_red_iterate`, `isBlock`, `equiv1`. These already retain the complete list. |
| Physical sums and boundaries | `OccurrenceNewborn.lean`: `physicalLength`, `physicalLength_append`, `physicalLength_nonneg`, `physicalLength_of_equiv1`, `physicalLength_flatten`, `factorBoundary`, `factorBoundary_mono`, `factorBoundary_succ`. Strict positivity and cardinality of the selected starts still need the small new adapter. |
| Actual mark interfaces | `OccurrenceFinite.lean`: `markAt`, `markAt_before`, `markEquiv`; `OccurrenceTransport.lean`: `parikhZ_append`, `parikhZ_eq_of_equiv1`, `equiv1_of_parikhZ_eq`. These support literal witnesses and prefix-vector injectivity. |
| Strict cut labels | `StrictSystem.lean`: `cut_follow`, `cut_follow_index`, `cutPair_ne`; named adapter `NamedCutProximity.strict_cut_labels`. |
| Exact named physical scaling | `NamedStableChart.physical_row_pos`, `beta_gt_two`; `NamedGeometricEnclosure.physicalLength_subst`, `physicalLength_iterateImages`. Extend the displayed word recurrence over arbitrary powers; do not introduce a frequency premise. |
| Eventual open-cover containment | Worktree `NamedCutNeighborhood.eventually_cutPoints_subset` for all distinct pairs; `carrierOverlap_compact`, `eventually_carrierOverlap_strict_cuts_mem`, and `finite_carrierOverlap_cover_captures_strict_cuts` for exactly the represented `CutPair C` labels. Their final acceptance is separate from this plan. |
| Misleadingly similar results | `StrictSystem.mismatch_density` counts unequal letters at positions, not balanced cuts. `CountBridge.lean` identifies scattered-subword count definitions. Neither is a lattice-point counting theorem. |

Suggested module boundary after a fresh targeted gate: `StrictCutCount.lean`
for actual reduction starts, finite integer cut sets, cardinality and the
physical inequality; a small named specialization can use the existing
chart and neighborhood theorems. Formal controls should retain repeated
state occurrences, initial/terminal endpoint conventions, and a mismatch
position whose two prefix Parikh vectors are unequal.

## What remains on the analytic side

For M1, the necessary counting interface can be weaker than the written
equality (2). For each **fixed** bounded regular cylinder union `U`, it
suffices to prove, at the original translation parameter,

\[
\forall\eta>0\;\exists X_0\;\forall X\ge X_0:\quad
N_U(X)\le X\bigl(\mu(U)/\kappa+\eta\bigr),
\]

where `N_U(X)` counts integer `z` satisfying `0 ≤ ℓz < X` and `star z ∈ U`.
The set being counted must be proved finite before using its natural
cardinality. The window and all residue depths are fixed before taking
`X → ∞`; `X_n` may then be substituted. This upper bound, the finite cut
lower bound, and regular outer approximation would give the written
measure inequality. None of those steps may be replaced by a positivity
assumption on the tiles or overlap.

The precise unfilled analytic inputs are:

- **All-depth cylinder normalization.** `MadicHaar.measure_first_kernel`
  and `NamedProductHaar.first_residue_card` prove the first-level facts.
  Generalize the same surjective-evaluation/fiber-partition argument to
  depth `q`, prove `Nat.card (Residue M q) = 2^q`, and obtain each original
  carrier cylinder's probability `2^(-q)`. No switch to `H_(M^q)` is needed.
- **Actual covolume binding.** `NamedStableChart.reconstruction`, `kappa_pos`
  and `physical_r_eq_kappa` are algebraic chart facts. They do not establish
  a lattice fundamental domain or a Haar covolume. Bind the chart matrix
  with rows `physicalRow`, `W 0`, `W 1` to an actual lattice and its
  Lebesgue covolume. The candidate determinant is `-kappa`; the determinant
  calculation and its measure interpretation must both be proved.
  Mathlib's `ZLattice.covolume_eq_det` and index/covolume theorem are relevant.
- **Deterministic strip counting.** No repository declaration found in this
  audit proves the fixed-origin, fixed-width strip asymptotic. The existing
  rational-independence lemma `OccurrenceNewborn.rational_length_injective`
  is a reusable algebraic input under its explicit irreducible-characteristic
  and eigenrow hypotheses; it is not an equidistribution theorem. A source-
  bound torus/character argument still needs its actual dense direction,
  averaging, normalization and regular-window approximation proved.
- **Regular outer-cover measure control.** The new finite open-subcover
  theorem is topological. Selecting a regular cylinder union whose measure
  approaches that of the compact intersection union is a separate measure
  argument. Arbitrary measurable or half-open covers do not automatically
  satisfy its neighborhood hypothesis.

`NamedProductHaar.measure_product_action` and `measure_affine_power` already
prove the correct nonunit factor `beta⁻¹`. `NamedOverlapHaar` gives finite
overlap mass and upper bounds from literal history covers. None supplies
the count above or a positive lower bound. `PhysicalMass.lean` is finite
graph transpose-budget algebra, not physical-space lattice density.

The current neighborhood change also includes `carrierOverlap`, indexed
by exactly the represented `CutPair C` labels, with compactness, eventual
strict-cut containment and finite-open-cover corollaries. I inspected that
adapter: finite quantification over sources and labels is preserved, and
`strict_cut_labels.1` supplies each actual cut's represented label. This
matches written M1's support; using both ordered orientations does not
change the union of symmetric intersections. Keep it distinct from
`overlapUnion`, which includes all six distinct ordered pairs. The original
integer cut-cardinality inequality remains the next finite obligation.

## Primary-source guard and reproducible inspection

Read both written notes:
`docs/c4-nonunit-madic-counting-bridge-2026-11-04.md` (especially §§2,4) and
`docs/c4-nonunit-residue-occupancy-2026-11-04.md` (Lemma R1). Their written
M1/R1 arguments are **not compiled Lean proofs**.

[Moody, Theorem 1](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/2304DD08EC0AD970DEF94D7C180C4752/S0008439500015630a.pdf/div-class-title-uniform-distribution-in-model-sets-div.pdf),
printed pp.124–126, was inspected directly: the general measurable-window
claim is almost sure in the translation parameter; the all-parameter
conclusion additionally uses zero boundary measure and the stated
cut-and-project/averaging hypotheses. An almost-everywhere theorem cannot
certify the original cut origin.

[Mathlib's lattice covolume API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/ZLattice/Covolume.html)
was checked against pinned source
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.
`ZLattice.covolume.tendsto_card_div_pow` counts isotropically dilated lattice
windows with dimension-power normalization. It does not directly apply to
the present strip, where only the physical interval grows and the stable
window stays fixed.

Reproduce the bounded source audit from the checkout root:

```bash
rg -n 'mem_of_red_iterate|cut_follow|mismatch_density|maxLen' proof/PscVerif/PscVerif/StrictSystem.lean
rg -n 'physicalLength|factorBoundary|rational_length_injective' proof/PscVerif/PscVerif/OccurrenceNewborn.lean
rg -n 'physicalLength_subst|physicalLength_iterateImages' proof/PscVerif/PscVerif/NamedGeometricEnclosure.lean
rg -n 'cutPoints|eventually_.*cuts|finite_open_cover' proof/PscVerif/PscVerif/NamedCutNeighborhood.lean
rg -n 'covol|equidistrib|lattice|density' proof/PscVerif/PscVerif
rg -n 'measure_first_kernel|first_residue_card|measure_product_action|measure_affine_power' proof/PscVerif/PscVerif/MadicHaar.lean proof/PscVerif/PscVerif/NamedProductHaar.lean
rg -n 'covolume_eq_det|tendsto_card_div_pow' proof/PscVerif/.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Covolume.lean
```

This plan stops at a concrete finite-count target and the explicit analytic
boundary. It promotes no measure positivity, M1, general C4, or PSC claim.
