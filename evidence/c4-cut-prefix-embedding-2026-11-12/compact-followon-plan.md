# Proposed next step: compact-cover transfer

Preparatory source analysis of `research/c4-cut-prefix-embedding` at
`73a0b6a95539beb1b6712afec0f8412571b41cd3`. This is a proof plan: no new Lean
declaration has been implemented or checked.

## Exact missing statement

Fix a named fixture, put `M := incidenceLinear (substitution fixture)`, and write
`G := Stable × MadicResidue.Carrier M`. For `ε > 0` and `q : ℕ`, define the
proximity relation mathematically by

\[
R_{\varepsilon,q}(x,y)\iff
\|x_1-y_1\|<\varepsilon
\quad\text{and}\quad
\operatorname{eval}_q(x_2)=\operatorname{eval}_q(y_2).
\]

The generic transfer lemma needed is:

> If `K, L ⊆ G` are compact, `U` is open, and `K ∩ L ⊆ U`, then there are
> `ε > 0` and `q : ℕ` such that, for every `x : G`, the existence of
> `y ∈ K` and `z ∈ L` with `R ε q x y` and `R ε q x z` implies `x ∈ U`.

This gives containment in an arbitrary **open neighborhood of the
intersection**, not membership in the intersection. It also covers an empty
intersection with `U = ∅`. For an open cover, apply it to the union of the
covering sets. A cover by arbitrary measurable or half-open cylinders needs a
separate neighborhood argument; containment of the intersection alone is not
enough for those sets.

## Actual topology and available compactness

`OccurrenceResidue.Ambient` is exactly the product above, with
`NamedStableChart.Stable = Fin 2 → ℝ`. `MadicResidue.Carrier M` is the subtype of
compatible sequences in `∀ q, Residue M q`. Each coordinate has the discrete
topology; the carrier inherits the product topology, not a discrete topology
on the inverse limit. These are Hausdorff additive topological groups.

`NamedPrefixCompact.tiles_compact fixture a` already proves compactness of
every actual named prefix tile, using its proved stable window and the
compact matrix-adic carrier. Thus the transfer lemma requires **no additional
precompact bound on the common cut points and no local-compactness
hypothesis**. Compact tiles and the compatible product uniformity suffice.
The topology-only proof below avoids installing a new explicit uniform-space
instance; the current residue module does not declare one.

## Short proof route

1. Use `IsOpen.mem_nhdsSet` and `IsCompact.nhdsSet_inter_eq` to turn
   `K ∩ L ⊆ U` into `U ∈ 𝓝ˢ K ⊓ 𝓝ˢ L`. By
   `Filter.mem_inf_iff_superset`, obtain neighborhoods `W_K` of `K` and
   `W_L` of `L` with `W_K ∩ W_L ⊆ U`.

2. Compactness makes translation into each neighborhood uniform over its
   tile. Apply `IsCompact.eventually_forall_of_forall_eventually` at `0` to
   the predicate `y + d ∈ W_K`. Continuity of addition and
   `mem_nhdsSet_iff_forall` supply its local premise at every `y ∈ K`.
   Obtain a zero-neighborhood `V_K` with `K + V_K ⊆ W_K`; do the same for
   `L`, and intersect the two zero-neighborhoods. Consequently,
   `(K + V) ∩ (L + V) ⊆ U`.

3. Establish the small missing neighborhood-basis lemma: every
   `V ∈ 𝓝 (0 : G)` contains

   \[
   V_{\varepsilon,q}=
   \{d:\|d_1\|<\varepsilon,\ \operatorname{eval}_q(d_2)=0\}
   \quad\text{for some }\varepsilon>0,q\in\mathbb N.
   \]

   Use `nhds_prod_eq`, `nhds_subtype`, `nhds_pi`, and `Filter.mem_pi'`.
   A product neighborhood restricts only finitely many residue coordinates.
   Refine each discrete-coordinate neighborhood to its zero singleton and
   take `q` to be the maximum restricted index (use `0` if empty).
   `MadicResidue.reduction_eval` shows zero at `q` implies zero at every
   restricted depth. The stable factor supplies a norm ball. Conversely,
   each displayed set is a zero-neighborhood by
   `MadicResidue.continuous_eval` and discreteness.

4. From `R ε q x y`, additivity gives `x - y ∈ V ε q`; hence
   `x = y + (x - y) ∈ K + V`. Repeat for `z ∈ L` and conclude `x ∈ U`.

An alternative after providing a compatible uniform-space instance is
`IsCompact.nhdsSet_basis_uniformity` together with
`IsCompact.nhdsSet_inter_eq`; the translation proof uses existing topology
directly and has fewer instance obligations.

## Applying the lemma to literal balanced cuts

Let
`I := ⋃ a, ⋃ b ≠ a, tiles fixture a ∩ tiles fixture b`.
Given an open `U` containing `I`, apply the generic lemma to each of the six
ordered distinct-letter pairs. Take a positive minimum of the finitely many
ε values and a maximum of their q values. Reduction compatibility makes the
larger q sufficient for every pair. Three unordered pairs would also suffice,
but six ordered pairs match the existing cut labels directly.

**Choose this ε and q before choosing the generation threshold.** For each
fixed source pair `(u,v)`, use
`NamedCutProximity.eventually_all_prefixes_close` for both words and take the
maximum threshold. Its authenticated prefix witnesses lie in their
respective tiles. Exact balance identifies their common cut vector, and
`OccurrenceResidue.residue_ambientStar` translates the existing quotient
equalities into `R ε q`. The theorem already ensures the fixed depth is
eligible once `n ≥ N`, with inflation exponent `12*n`.

`NamedCutProximity.strict_cut_labels` supplies distinct letters for cuts of a
supplied strict carrier. For a fixed finite strict carrier `C`, a further
finite maximum gives one threshold for all `T ∈ C` and all their actual
balanced-cut marks. This uses fixed finite source words; it does not allow
sources to grow with the inflation generation.

The resulting named theorem should state eventual containment of **all such
cut points in `U`**, uniformly over the chosen finite carrier. It supplies no
lattice count, covolume normalization, Haar lower bound, or positivity claim.

The subsequent count must count the original common Parikh cut vectors `x`.
The witness ordinal `j` is not asserted to be injective in the original
parent position: two parents with the same letter and local digit use the
same anchor and may produce the same `j`. The finite source correction
retains their difference. Witnesses establish proximity; their number of
distinct ordinals is not a substitute for the physical cut-point count.

## Source map for implementation

Repository-relative modules are under `proof/PscVerif/PscVerif/`:
`MadicResidue.lean`, `OccurrenceResidue.lean`, `NamedPrefixCompact.lean`, and
`NamedCutProximity.lean`.

The checked Mathlib source is pinned at
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09` and is available after provisioning
under `proof/PscVerif/.lake/packages/mathlib/`:

| File | Useful declarations |
| --- | --- |
| `Mathlib/Topology/Separation/Hausdorff.lean` | `IsCompact.nhdsSet_inter_eq` |
| `Mathlib/Topology/Compactness/Compact.lean` | `IsCompact.eventually_forall_of_forall_eventually`, `IsCompact.mem_nhdsSet_prod_of_forall` |
| `Mathlib/Topology/NhdsSet.lean` | `IsOpen.mem_nhdsSet`, `mem_nhdsSet_iff_forall` |
| `Mathlib/Order/Filter/Basic.lean` | `Filter.mem_inf_iff_superset` |
| `Mathlib/Topology/Constructions.lean` | `nhds_subtype`, `nhds_pi` |
| `Mathlib/Order/Filter/Pi.lean` | `Filter.mem_pi'` |
| `Mathlib/Topology/UniformSpace/Compact.lean` | `IsCompact.nhdsSet_basis_uniformity` (alternative route) |
