# Pre-code stop/go: compact neighborhoods of actual cut overlaps

Date: 2026-11-12. Baseline: `main@bdf033f647f73f911a47260e8bdad5f2e96f3c7a`,
tree `73201424138427d63ddf05c9c1102f424af5b1af`.

**Decision: GO with the narrowed topological transfer below.** The argument
is standard compact-set neighborhood theory. The contribution is its
formal specialization to the repository's actual product carrier and the
literal balanced cuts already handled by `NamedCutProximity`. No new
topological principle or positive-measure result is claimed.

This decision precedes new theorem code. `AGENTS.md`, the relevant
side-notes ledger entries, and the archived
`evidence/c4-cut-prefix-embedding-2026-11-12/compact-followon-plan.md` were
read. The new baseline retains the inspected `MadicResidue`,
`NamedPrefixCompact`, and `NamedCutProximity` sources unchanged.

## Exact proposed claims

Let `M` be an integer-module endomorphism, let `H_M` be the existing
`MadicResidue.Carrier M` with its induced product topology, and let `E` be a
normed additive commutative group. Put `G := E × H_M` and

\[
R_{\varepsilon,q}(x,y)\iff
\|x_1-y_1\|<\varepsilon\ \land\
\operatorname{eval}_q(x_2)=\operatorname{eval}_q(y_2).
\]

1. **Product neighborhood basis.** Every neighborhood of `0 : G` contains
   `{d | ‖d.1‖ < ε ∧ eval M q d.2 = 0}` for some `ε > 0` and natural depth
   `q`; every such set is itself a neighborhood of zero.
2. **Compact intersection transfer.** Given compact `K,L ⊆ G` and an open
   `U` containing `K ∩ L`, there exist `ε > 0,q` such that, for every
   `x : G`, witnesses `y ∈ K,z ∈ L` satisfying both `R ε q x y` and
   `R ε q x z` imply `x ∈ U`.
3. **Named finite-carrier consequence.** Fix a fixture, a finite word-pair
   carrier `C`, and an actual `StrictSystem (substitution fixture) C`.
   Write `I` for the union of the six ordered distinct-letter tile
   intersections. For every open `U ⊇ I`, there is one `N` such that, for
   every `T ∈ C`, every `n ≥ N`, and every pair of actual marks in the
   `12*n` inflations of `T.1,T.2` with equal prefix Parikh vectors, their
   common `ambientStar` cut point belongs to `U`.

The third claim is conditional on the supplied strict system. It does not
construct one. A fixed-source variant may instead assume the two actual
following letters are distinct explicitly. A finite-open-subcover corollary
uses compactness of the finite union of these intersections and the standard
`IsCompact.elim_finite_subcover` before applying this same transfer.

## Six primary sources checked

The four Mathlib documentation pages below were inspected online. The exact
declarations were also read in the repository-pinned Mathlib source at
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`; that pin, rather than a moving
documentation build, controls implementation.

1. **Mathlib, compact intersection neighborhoods:**
   [Topology.Separation.Hausdorff](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Separation/Hausdorff.html#IsCompact.nhdsSet_inter_eq),
   `IsCompact.nhdsSet_inter_eq`. For two compact sets in a Hausdorff space,
   the neighborhood filter of their intersection is the infimum of their
   neighborhood filters. This is the strongest directly matching imported
   result; arbitrary sets only have the one-sided inequality.
2. **Mathlib, uniformity over a compact parameter:**
   [Topology.Compactness.Compact](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html#IsCompact.eventually_forall_of_forall_eventually),
   `IsCompact.eventually_forall_of_forall_eventually` and the stronger
   `IsCompact.mem_prod_nhdsSet_of_forall`. Applied to `y + d ∈ W` at
   `(0,y)`, these turn continuity of addition and a compact set `K` into
   one zero-neighborhood `V` satisfying `K + V ⊆ W`.
3. **Mathlib, induced and product topology:**
   [Topology.Constructions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Constructions.html),
   `nhds_subtype` and `nhds_pi`. These identify the neighborhood filters
   used by the actual compatible-sequence subtype. They do not declare
   the entire inverse limit discrete.
4. **Mathlib, finite-coordinate product neighborhoods:**
   [Order.Filter.Pi](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Pi.html#Filter.mem_pi'),
   `Filter.mem_pi'`. A neighborhood in the countable product restricts
   only finitely many coordinates. Discreteness lets those restrictions
   be refined to zero singletons; compatibility reduces the finite list
   to its maximum depth.
5. **Minervino and Thuswaldner, non-unit prefix-closure geometry:**
   [*The geometry of non-unit Pisot substitutions*](https://arxiv.org/pdf/1402.2002),
   Section 7, Lemma 7.5, Theorem 7.7 and Remark 7.8. The established
   terminology is Rauzy subtiles, prefix/numeration constructions and
   internal spaces including finite places. Their identifications use
   their specified number-field representation. This supplies context,
   not an identification of the repository's `H_M` with that space or a
   transferred tiling/measure theorem.
6. **Moody, the later counting boundary:**
   [*Uniform Distribution in Model Sets*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/2304DD08EC0AD970DEF94D7C180C4752/S0008439500015630a.pdf/div-class-title-uniform-distribution-in-model-sets-div.pdf),
   Section 2 and Theorem 1, printed pages 124–126. The paper assumes a
   cut-and-project lattice and specified averaging hypotheses. Its
   arbitrary relatively compact measurable-window conclusion is almost
   sure in the translation parameter; the all-parameter statement has
   the additional zero-boundary-measure hypothesis. Neither applies to
   a fixed original cut count merely because nearby tile witnesses exist.

## Hypotheses that transfer and the short reduction

The actual carrier is a subgroup of a product of discrete quotient groups,
so it is a Hausdorff topological group. `E` supplies norm-ball
neighborhoods. For the generic basis and transfer, no injectivity or
finite-quotient assumption on `M` is needed once compactness of `K,L` is
given. For the named application, the necessary compactness is already
the theorem `NamedPrefixCompact.tiles_compact`; its existing arithmetic
and stable-window proof remains the source of that fact.

Start with `U ∈ 𝓝ˢ (K ∩ L)`. Source 1 and
`Filter.mem_inf_iff_superset` give neighborhoods `W_K,W_L` whose
intersection lies in `U`. Source 2 gives a common zero-neighborhood `V`
with `K + V ⊆ W_K` and `L + V ⊆ W_L`. Sources 3–4, `nhds_prod_eq`, and
`MadicResidue.reduction_eval` refine `V` to one stable ball and one residue
depth. The proximity assumptions put `x-y` and `x-z` in `V`, giving the
desired containment. `MadicResidue.continuous_eval` proves each residue
kernel is open in the existing topology.

**No separate precompact bound on the common cut points and no
local-compactness hypothesis are needed.** Compactness is applied to the
tile witnesses. This proof can use topology directly, without introducing
a new uniform-space instance or a sequential-compactness argument.

For each fixed distinct-letter pair, choose epsilon and depth before
invoking `NamedCutProximity.eventually_all_prefixes_close` for the fixed
source words. `Filter.eventually_all` then combines the six pair predicates,
and `Finset.eventually_all` combines the fixed finite source carrier. These
finite filter operations give one common eventual threshold without choosing
a separate explicit minimum of epsilon values. Exact balance supplies
one common cut vector; `OccurrenceResidue.residue_ambientStar` identifies
its quotient coordinates, and `NamedCutProximity.strict_cut_labels`
supplies distinct following letters. Depth is fixed before `N`; reduction
permits shallower comparison, never unsupported deeper comparison.

## Negative controls and retained boundaries

- **Containment alone is insufficient:** in `ℝ × H_M`, take
  `K=L={(0,0)}` and the non-neighborhood `U=K`. Nonzero real points with
  zero carrier coordinate approach both tiles at every residue depth
  but remain outside `U`. The target must be an open neighborhood, not
  an arbitrary measurable cover or exact intersection membership.
- **A fixed coarse depth cannot control all neighborhoods:** for the
  existing doubling carrier on `ℤ`, `star(2^q)` agrees with zero at depth
  `q` and differs at `q+1`. With equal zero stable coordinates and
  singleton zero tiles, the open depth-`q+1` zero cylinder excludes that
  point. Reuse the genuine-carrier controls already in `CutPrefixControls`.
- **Do not erase compactness/closedness:** `K={0}` and `L=(0,1)` in the
  real factor have empty intersection but can be approached
  simultaneously at arbitrary precision. Even with `U=∅` open, the
  unrestricted-set version is false. These are abstract interface
  counterexamples, not standing-Pisot counterexamples.
- **Closedness alone is insufficient without compactness:** the real-plane
  axis `y=0` and hyperbola `xy=1` are closed and disjoint, yet `(R,0)`
  and `(R,1/R)` approach each other as `R` grows.
- **Pointwise convergence over an infinite source family is insufficient:**
  `x_n(i)=1` when `i=n`, zero otherwise, eventually vanishes for every fixed
  `i` but never uniformly for all `i`.
- **Empty intersections remain admissible:** applying the valid lemma
  with `U=∅` gives eventual absence of simultaneous approximants. Do not
  insert nonemptiness or positive measure as an implicit premise.
- **Quantifiers remain uniform only over fixed finite data:** the open
  set determines epsilon/depth, and the fixed carrier determines the
  eventual threshold. The previous growing-source-bound counterexample
  remains relevant. The source/reference identities remain those of
  each actual named word.

## Narrowed implementation and non-claims

Proceed with a reusable neighborhood-basis/compact-transfer layer, the
named finite-carrier adapter, and proportionate formal controls. This is
deductive Lean work using already established proximity; no new numerical
census or executable mathematical algorithm is needed for this target.
Preserve the full isolated source build, compiled axiom audit, exact source
provenance and the required Work shown sections for acceptance.

An open cover may be replaced by its open union. A regular or half-open
cylinder cover requires a proved neighborhood inclusion before this lemma
can consume it. The fixed-origin lattice count, correct product Haar
normalization/covolume, original strict-cut density, outer-cover measure
argument and positive overlap remain separate obligations. In particular,
count original common Parikh cut vectors; the anchored reference ordinals
need not be injective. No all-packet identification, general C4, PDS, BH,
or PSC status is promoted, and no independent human review is claimed.
