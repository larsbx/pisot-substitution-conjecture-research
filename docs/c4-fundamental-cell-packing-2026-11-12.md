# Actual matrix-adic fundamental cells and finite packing

Date: 2026-11-12. This increment follows PR #560 at
`d6d6ba2331bc119282a9b18170053c4eb24a9346`. It implements the exact-cell,
common-mass, shrinking-internal-width and finite-packing portion of the
[committed pre-code decision](c4-finite-cut-count.md#pre-code-decision-for-the-following-increment).
The [primary-source review](../evidence/c4-finite-cut-count-2026-11-12/future/cell-packing-literature-review.md)
and [actual-model review](../evidence/c4-finite-cut-count-2026-11-12/future/cell-packing-route-review.md)
were committed before these six modules were written. Fundamental-domain
measure equality and finite packing are standard; the work here binds them
to the original integer indices, actual matrix-adic carriers and named
physical/stable chart.

## Result and scope

For either named substitution, let `M` be its actual integral incidence,
`H = MadicResidue.Carrier M`, and `ν` any additive Haar probability measure
on that carrier. Let `E = Fin 2 → ℝ`,
`μ = volume_E.prod ν`, and `λ = volume_ℝ.prod μ`. The full chart is

\[
\Phi(x)=(\ell x,Wx),\qquad
\gamma(z)=(\ell z,Wz,\operatorname{star}(z)).
\]

The proof constructs, after reassociating products,

\[
F_q=\Phi(M^qQ)\times\ker(\operatorname{eval}_q),
\qquad Q=\prod_{i=0}^{2}[0,1).
\]

Every `F_q` is a measurable fundamental domain for the **same** original
`ℤ³` translation action. Their common measure is `ENNReal.ofReal c` for
one real number `c > 0`, independent of `q`. No numerical value of `c`
is asserted.

The main assembled interface,
`NamedFundamentalCell.exists_positive_uniform_packing`, fixes that `c`
first. For every zero neighborhood `V` in `E × H`, it supplies `N` such
that every block depth `q = 12*n`, `n ≥ N`, supports the following bound.
For any finite set `Z` of original integer vectors, `X ≥ 0`, and sets
`U, O` satisfying

\[
0\le\ell z<X,\quad\gamma(z)_{\mathrm{internal}}\in U\ (z\in Z),
\qquad U+V\subseteq O,
\]

with `O` measurable and `μ(O) < ∞`,

\[
\boxed{c\,\#Z\le (X+L_q)\,\mu(O)},
\qquad L_q=\beta^q\sum_i\ell_i.
\]

The formal right-hand side uses `μ.real O`. The finite-measure hypothesis
justifies the conversion from extended nonnegative measure to this real
quantity. `U` and `V` need not be measurable. The argument measures only
the measurable translated cells and a containing measurable rectangle.

This is a finite upper bound. It supplies neither a lattice asymptotic
nor positive measure of a represented-pair overlap by itself.

## Assumptions and hypotheses

The generic cell construction has an integral linear map `M`, an
invertible real extension `A`, an invertible continuous linear chart
`phi`, and the explicit compatibility equation
`A (intCast z) = intCast (M z)`. Injectivity of `M` follows from these
assumptions. The proof uses the actual compatible-sequence carrier for
`M`, rather than a substitute finite-place model.

The named specialization discharges compatibility from each fixture's
proved `incidence_eq`. The same real matrix serves both fixtures, while
each literal substitution retains its own `H`. Its determinant is two;
the explicit real inverse is proved in `NamedFullChart`. The inverse of
the full physical/stable chart uses the existing reconstruction identity.
The stable projection alone is not used as an invertible chart.

The named measure results quantify over `ν` with the explicit assumptions
`ν.IsAddHaarMeasure` and `IsProbabilityMeasure ν`. They construct
translation invariance for the actual product measure. The full chart is
not claimed to preserve the canonical real volumes. Only the
parenthesis-changing `view` uses a product measure-preserving equivalence.

For packing, the finite set, strip, target finiteness and enclosure
hypotheses remain explicit. A later cut consumer must supply them using
its actual original-integer cut set. No carrier, strictness or factor
bound is silently inferred by this increment.

## Derivation / reduction

### Exact representatives and matching depths

For a full point `(r,h)`, first choose an original integer `z₀`
representing `eval_q h`. Reduce
`(A^q)⁻¹ (phi⁻¹ r - intCast z₀)` coordinatewise by integer floors.
If the resulting integer is `k`, the correcting diagonal vector is
`z₀ + M^q k`. The remaining real point lies in `phi(A^q Q)` and its
residue at the same depth is zero.

If two points of one cell differ by a diagonal integer vector `z`, the
residue condition forces `z = M^q k`. Applying the inverse real chart and
the inverse real power then gives two points of `Q` differing by `k`.
Their coordinatewise floors are zero, so `k = 0` and `z = 0`. This proves
exact uniqueness and literal pairwise disjointness, including boundary
points under the half-open convention.

Measurability follows from the coordinatewise half-open cube, continuous
linear equivalences and the actual residue evaluation. Coverage and
uniqueness construct Mathlib's `IsAddFundamentalDomain` for the original
countable action.

### One positive finite mass

Every cell is contained in the full-chart image of the corresponding
closed real cube, times the compact carrier. Hence its product Haar
measure is finite. The ambient product measure is nonzero. A fundamental
domain for a countable measure-preserving action cannot have measure zero
under that nonzero measure: its countable translates cover the space.
Mathlib's fundamental-domain measure equality then gives the same
positive finite mass at all depths.

This implementation uses coverage to obtain positivity. It therefore
does not need a separately constructed open subset of `F₀`, nor a
determinant/index calculation for the exact value of `c`.

### Intrinsic widths

Positive entries of `physicalRow` bound the physical coordinate on the
closed cube by `∑ i, physicalRow i`. The eigenvector identity then proves
`0 ≤ x_physical ≤ L_q` for every point of `F_q`.

One depth-independent bound on the stable image of the closed cube is
`β`. The existing block-twelve contraction gives

\[
\|x_{\mathrm{stable}}\|\le(7/8)^n\beta
\qquad(x\in F_{12n}).
\]

If `m ≤ q`, the actual reduction maps give `eval_m x_H = 0` for every
`x ∈ F_q`. Combining these two facts with the original product
neighborhood basis proves uniform internal containment in any fixed zero
neighborhood for all sufficiently deep block cells. The physical width
may grow; it is finite at each chosen depth.

### Finite measure packing

The translated cells indexed by `Z` are disjoint and each has mass `c`.
Their union therefore has mass `c * Z.card`. After the product
reassociation, the strip and width bounds put that union in
`[0, X + L_q] × O`. Monotonicity, product measure and the length of a real
closed interval give the displayed inequality.

The final theorem fixes `V` before its cell-depth threshold and quantifies
over `Z` and `X` only afterwards. A later argument may fix one such depth
and let word generation grow. The theorem supplies no relative-growth
estimate for `L_q / X` when `q` varies with `X`; the planned limiting
argument fixes `q` before letting the strip length grow.

## Modules

| Module | Role |
|---|---|
| `MadicFundamentalCell` | Coordinatewise cube, exact representatives, literal disjointness, compact containment, measurable fundamental domains and diagonal invariance constructors. |
| `FundamentalCellPacking` | Generic common positive mass and finite-translate rectangle estimates. |
| `NamedFullChart` | Actual physical/stable continuous linear equivalence and real incidence equivalence. |
| `NamedCellBounds` | Intrinsic physical width, fixed stable cube bound, residue reduction and uniform internal shrinkage. |
| `NamedFundamentalCell` | Fixture-specific original carriers, actual product Haar measure, common mass and assembled finite packing. |
| `MadicFundamentalCellControls` | Exact cube-face and mismatched-depth counter-calibrations. |

## Negative controls

The product-order interval `Set.Ico (0 : Fin 3 → ℝ) 1` is bounded but
contains `(1,0,0)`. The coordinatewise cube excludes that upper-face
point. The control proves a nontrivial integer-translate intersection for
the product-order interval, so it cannot replace `Q` in the exact
uniqueness argument.

Two controls use the actual original-carrier construction for `M = 2I`.
A real depth-one cell paired with a depth-zero residue condition overlaps
its translate by the first basis vector. A real depth-zero cell paired
with a depth-one residue condition fails to cover the full point
`(0, star e₀)` under every original integer translate. Thus disjointness
and coverage enforce matching depths in opposite directions. These are
non-Pisot calibration examples; they make no claim about the named
strict-overlap obstruction.

The earlier failed implementation attempts are retained as development
history. They concern Lean API, simplification and typeclass assembly;
they provide no full-gate acceptance.

## Evidence and replay

The source publication records the focused checks and source review as
development evidence. Required acceptance remains the unchanged complete
isolated verifier at the exact published code revision:

```sh
./tools/check_lean.sh
```

That verifier prepares an isolated source workspace, checks the pinned
Lean and Mathlib identities, obtains a fresh source-keyed upstream cache,
builds the complete aggregate and audits compiled declarations. The final
evidence supplement must record the actual terminal exit, exact source
revision/tree, raw log digest, declaration inventory and full transitive
axiom allowlist. Focused development artifacts do not replace that gate.

At the initial source publication this complete acceptance is pending.
No hosted result is asserted for a future revision. The evidence-only
child will distinguish its own identity from the tested code parent.

## Non-claims / remaining gaps

The next mathematical consumer still needs to combine compact-overlap
capture and the original finite lower count with a small open target,
a uniform additive neighborhood, positive source length and growth of
the physical strip. Outer regularity and the exact product-model
topological instances must be discharged there. That assembly is not
present in these six modules.

There is no claimed positive Haar measure of `carrierOverlap`, no
per-pair frequency, no numerical normalization of `c`, no degree-one
tiling or model-set asymptotic, and no general C4 or Pisot-substitution
closure. No governed claim status is promoted. Independent human review
remains validation debt; this draft contribution is not described as
independently human reviewed.
