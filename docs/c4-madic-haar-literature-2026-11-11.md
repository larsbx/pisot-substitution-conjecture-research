# Haar scaling on the original matrix-adic carrier

Decision on 2026-11-11: proceed with a direct inverse-limit argument on the
carrier at #547 revision `e1033f3d9b5fc9c9424d10e12f0e44b63135be03`.

- [Minervino and Thuswaldner, The geometry of non-unit Pisot substitutions](https://aif.centre-mersenne.org/item/10.5802/aif.2884.pdf), §3, gives the product-formula modulus in a representation built from completion fields.
- [Rossi, Steiner and Thuswaldner, Rational self-affine tiles](https://arxiv.org/abs/2110.09112) uses an archimedean/solenoidal product and finite residue classes. Its expanding-matrix hypotheses do not transfer to the original stable chart.
- [Stacks Project, tag 08ZY](https://stacks.math.columbia.edu/tag/08ZY) gives the compact Hausdorff topology of profinite limits. The range computation below requires a compatible division construction in the repository's specific quotient system.

The target is the standard finite-index Haar argument on the actual compact
subgroup. No identification with the full field product is assumed. In
particular, the finite-level action can fail to be injective, and multiplication
on the full field is surjective. Both would give the wrong model for the
image index of the actual compact limit.
