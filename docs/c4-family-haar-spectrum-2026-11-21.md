# Haar measure and inflation for the literal σₖ family

The inspected [PR #649](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/649) head is `991caf49bca7303188bf6ccccfe5bc5a1269c770`. The merge to `main` at `f5ba148da001aab1d052a54790b05c847dc684f4` has the same tree, `24269819d3ba247b98da80bca8c44e186293ddc7`. The full-history solenoid is the closed subgroup of compatible torus histories. Its inflation shift is a homeomorphism. The finite certificates span a dense subspace of continuous functions, and each nontrivial represented character has an injective forward orbit for `k ≥ 1`. For `k ≥ 2` the ordinary legal hull has a nonempty open set of fibres sharing a fixed positive window.

## Source decision

- Kitchens and Schmidt, *Automorphisms of compact groups* (1989), Lemma 2.2, treat the correspondence between Haar ergodicity and infinite orbits of nontrivial irreducible representations. The existing unit-modulus characters and their dense span suffice here. Use finite Bessel sums and the Archimedean property for the invariant coefficient calculation. [Published article](https://doi.org/10.1017/S0143385700005290)
- Baker, Barge and Kwapisz, *Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces* (2006), Theorems 4.2 and 5.1 and Corollary 5.2, relate generic fibre multiplicity and the translation spectrum for their realization. Use the established open window and exact inflation semiconjugacy of the full-history factor here. [Published article](https://www.numdam.org/item/AIF_2006__56_7_2213_0.pdf)
- Barge and Kellendonk, *Proximality and pure point spectrum for tiling dynamical systems*, §2.2 and Theorem 5.4, distinguish proximal rank from the almost-everywhere geometric premise. Their measure argument also uses expanding windows, a positive-measure seed and inflation ergodicity. [Author preprint](https://arxiv.org/abs/1108.4065)
- The pinned Mathlib gives `Measure.addHaarMeasure`, `Measure.addHaarMeasure_self` and `AddMonoidHom.measurePreserving`. Its finite-group character orthogonality concerns a different measure. Use Haar translation invariance, `ContinuousMap.inner_toLp`, `ContinuousMap.toLp_denseRange` and `Orthonormal.sum_inner_products_le`. [Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/tree/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib)

Proceed with a direct proof for the actual objects. A nonzero certificate can represent the trivial character. The zeroth torus projection can identify histories distinguished by their full-history characters. The window argument uses the family geometry for `k ≥ 2`.

## Derivation

**Haar preservation.** Normalize additive Haar on the entire compact compatible-history group. The existing shift is a continuous surjective additive homomorphism, with inverse given by dropping the first history coordinate. Equal total masses give `measurePreserving_shiftS`.

**Orthogonality and completeness.** Choose a point where two distinct characters differ. Haar invariance makes the integral of their product with one conjugated equal to that integral multiplied by a scalar different from one. It therefore vanishes. A unit character has diagonal integral one. Continuous-map density carries the continuous character span to a dense span in Haar L². Certificate labels can repeat a represented function. Orthonormality is applied to the distinct orbit samples.

**Finite Bessel and ergodicity.** Koopman composition preserves inner products. The coefficient of a fixed vector is constant along an orbit. Bessel on `Fin N` bounds `N * |coefficient|²` by the squared norm of the fixed vector, so the Archimedean property forces each nontrivial coefficient to vanish. Subtract the constant component and apply density. The indicator of a strictly invariant measurable set is constant almost everywhere, yielding `ergodic_shiftS` for `k ≥ 1`.

**Singleton fibres.** For the open synchronization set W with shared radius r > 0, each union of images of W at depths at least N is open, positive and forward invariant. Haar ergodicity makes it conull. Bijective inflation and semiconjugacy pull any pair in a fibre above an image back to a fibre in W. Re-inflation enlarges its exact shared window by the corresponding expansion power. Over the countable intersection of the tails, the agreement holds on every natural-radius window. Window injectivity and factor surjectivity give a conull Gδ set of singleton fibres for `k ≥ 2`.

## Controls and next obligation

The redundant nonzero certificate produces identical orbit vectors at depths zero and one. The actual seam pair obstructs an everywhere-singleton statement. The identity on the full solenoid preserves Haar and has a proper invariant open set with both sides of positive measure. The endpoint audit also refuses removing the scope premise `k ≥ 2`.

Restrict the closed factor to the inverse image of the conull Gδ set. The closed bijection there gives a continuous inverse on the subspace. Measurably extend the inverse and use it to push Haar forward to the hull. Prove the translation and inflation invariance of that measure and the surjectivity of L² pullback. The resulting spectral conclusion concerns the translation flow.

## Replay

`tools/check_c4_parameter_family.sh` includes the new source and audit. [Source-pinned local acceptance](../evidence/c4-family-haar-spectrum-2026-11-21/acceptance.json)
