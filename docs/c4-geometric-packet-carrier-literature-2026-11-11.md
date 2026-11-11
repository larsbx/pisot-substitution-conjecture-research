# Geometric packet carrier: targeted stop/go — 2026-11-11

## Proposed claim

Formalize the bounded-lattice part of Theorem F2 in
[the finite-overlap carrier note](c4-finite-overlap-carrier-2026-11-05.md),
then discharge the represented-ancestor premise of the accepted literal
finite-history cover. The baseline is main
`2848e5f67b605669a550f362a1de4bf1c1529f7c`. This increment is independent
of the all-prefix compact-window work in open #543 and uses none of its
unaccepted Lean declarations.

Let G be an additive commutative group, star an additive map from Z^3 to G,
and K_a actual supplied subsets of G. Supply two additive real coordinate
maps c_0,c_1 and an authenticated common enclosure
`abs(c_i(x)) <= R_i` for every x in every K_a. Supply positive physical
letter lengths ell, a common upper bound H, and a full chart reconstruction

\[
z_j=U_{j0}\,\operatorname{offset}_{\ell}(z)
    +U_{j1}\,c_0(\operatorname{star}z)
    +U_{j2}\,c_1(\operatorname{star}z)
\]

for every integral vector z, interpreted in the reals. This exact
reconstruction is the faithfulness premise; it is not inferred from a
serialized matrix or assumed for a degenerate projection.

From physical interior and nonempty actual overlap derive

\[
|z_j|\le B_j
 = |U_{j0}|H+2|U_{j1}|R_0+2|U_{j2}|R_1.
\]

For certified natural bounds N_j with B_j <= N_j, construct the finite
packet domain consisting of all letter pairs, integral coordinates in
[-N_j,N_j], and the physical-interior predicate. Prove that every nonempty
inverse ancestor of every packet in this domain belongs to the same domain,
using positive exact image scaling. Compose this derived representation fact
with `OccurrenceCover.overlap_eq_iUnion_restrictedHistory` under its existing
injectivity, commutation, tile-equation and integral-range hypotheses.

## Sources and exact transfer boundaries

The standard geometric background was inspected for the earlier
[finite-carrier literature gate](c4-finite-overlap-carrier-literature-gate-2026-11-05.md).
The new review rechecks its scoped bounded-lattice assertion against the
actual mainline Lean interfaces and the pinned mathlib implementation.

| Primary source | Relevant result and boundary |
| --- | --- |
| [Thuswaldner, Unimodular Pisot substitutions and their associated tiles](https://www.numdam.org/item/JTNB_2006__18_2_487_0.pdf), Lemma 3.4 and Definition 3.6 | Bounding the Perron and contracting coordinates to obtain a finite contact graph is standard. Unimodular tiling and later coincidence hypotheses are not imported into the supplied nonunit additive model. |
| [Akiyama–Lee, Algorithm for determining pure pointedness of self-affine tilings](https://arxiv.org/pdf/1003.2898), potential-overlap bounds (2.8)–(2.10) and Theorem 4.1 | Finite potential-overlap graphs retain multigraph occurrence information. The tiling/Meyer assumptions of the PDS criterion are not supplied by this integer-box theorem. |
| [Minervino–Thuswaldner, The geometry of non-unit Pisot substitutions](https://arxiv.org/pdf/1402.2002), Lemma 3.1 and Theorem 8.3 | Actual occurrence-indexed set equations in a nonunit representation space give the background. No identification of this generic additive model with that representation space, measure normalization, or degree-one tiling is claimed. |
| [Accepted inverse occurrences](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/2848e5f67b605669a550f362a1de4bf1c1529f7c/proof/PscVerif/PscVerif/OccurrenceInverse.lean), `InverseOccurrence.interior` | Positive lengths, positive scale and exact image scaling propagate the typed physical strip backwards along the two actual incoming marks. The proposed carrier must filter by this interior predicate; a coordinate box alone cannot use this theorem at every source. |
| [Accepted actual overlap and cover](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/2848e5f67b605669a550f362a1de4bf1c1529f7c/proof/PscVerif/PscVerif/OccurrenceCover.lean), `overlap_eq_iUnion_restrictedHistory`, and its imported `OccurrencePiece.overlap` | The overlap is an intersection of two actual supplied sets. A witness gives a difference of two bounded coordinates. The restricted-history cover requires representation at every intermediate source, which is the conclusion to derive rather than a new premise to assume. All its geometric action and original tile-equation hypotheses remain explicit. |
| [Pinned mathlib finite products](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Data/Fintype/Pi.lean) and [integer intervals](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Data/Int/Interval.lean) | Actual local sources provide `Fintype.piFinset`, `mem_piFinset` and `Int.card_Icc`. The full finite box is constructed rather than assumed; its unfiltered packet size is `9 * product_j (2*N_j+1)`. Natural upper bounds exist by the Archimedean property. |

## Derivation

For x in the overlap of K_a with the translate of K_b, both x and
x-star(z) lie in the specified tiles. Additivity gives
`c_i(star z)=c_i(x)-c_i(x-star z)`, hence absolute value at most 2R_i.
Physical interior and ell_a <= H bound the absolute physical offset by H.
Apply the exact chart reconstruction and the triangle inequality to obtain
the three coordinate bounds, then cast the certified natural bounds to
integers to place z in the finite product of intervals.

For an inverse occurrence from p in the filtered domain to u, the accepted
inverse-interior theorem gives interior of u. If u has nonempty actual
overlap, the just-proved coordinate bound places u in the box. Therefore u
is represented in the same filtered domain. This is a global one-step
representation statement at every admitted source and so supports all
finite depths in the existing history-cover theorem. No finite search or
closure guess appears in the argument.

## Controls and hypotheses that must remain visible

- A projection with a nonzero invisible integer direction cannot bound all
  residuals; exact full-chart reconstruction is essential.
- The physical strip concerns admitted packets and their ancestry. It is
  not an emptiness test for every arbitrary translated internal overlap.
- A too-small chosen bound is inadmissible unless the displayed real bound
  is proved below it. Exhausting an implementation budget is still refusal.
- Coordinate enclosures and integer boxes are inclusive. Boundary contact
  cannot be discarded as an empty overlap.
- Actual paired marks and every occurrence history are retained. Equal
  endpoint packets do not identify different occurrence paths.
- The existing `00/11/22` inverse-closed but forward-leaking example remains
  valid. Incoming representation supplies no forward mass conservation or
  compact Haar loss witness.
- Missing actual tile equations, action injectivity or integral range
  reflection cannot be filled by this finiteness theorem.

## Decision and scope

**Proceed with this narrowed deductive integration.** Implement one new Lean
module, construct the finite packet domain, and derive its nonempty incoming
representation and finite-history cover from the stated chart and enclosure.
This is the formalization and integration of a standard bounded-lattice
argument, not new tiling or coincidence theory.

Neither compactness nor a Pisot condition is needed for the elementary
carrier lemma once its exact chart and enclosure have been supplied. Their
construction from an arbitrary Pisot substitution remains separate. No
actual named chart certificate, universal stable realization, common tile
attractor, Haar recurrence, strict-root positivity, C4, G1 or PSC result is
asserted by this increment. Exact-head isolated Lean compilation and the
compiled-declaration axiom audit remain acceptance gates.
