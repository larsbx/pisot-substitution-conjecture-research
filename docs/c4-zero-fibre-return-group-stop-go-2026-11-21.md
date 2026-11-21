# Zero-fibre anchor through the return-vector group: source decision

## Proposed claim

For the literal `sigma_k = (1, 0 1^k 2, 001)` with `k >= 2`, prove the
obligation left by the
[zero-fibre witness increment](c4-zero-fibre-witness-review-2026-11-21.md):

```text
every legal inflation-periodic U with x(U) in -ell(Z^3)
shares a labelled tile with a fixed zero-fibre tiling V.
```

The proposed route uses only what Lean already has: `hull_dense_eventual`
(two legal hull tilings sharing a tile are densely eventually coincident,
`k >= 2`), transitivity of eventual coincidence, and periodicity of the
zero fibre. For a hull tiling `T`, put

```text
H(T) = { w in R : T and T - w are densely eventually coincident }.
```

Claimed steps: `H(T)` is a subgroup of `R`; it contains every return vector
of `T`; inflation maps `H(T)` into `H(Phi T)` by multiplication with
`beta`; for this family it contains all three tile lengths; hence tilings
with tile starts in one coset of `ell(Z^3)` are densely eventually
coincident.

## Prior art and terminology

1. Barge, Štimac and Williams, *Pure discrete spectrum in substitution
   tiling spaces*, DCDS 33 (2013),
   [DOI](https://doi.org/10.3934/dcds.2013.33.579),
   [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf).
   Section 4 is the closest construction. The proof of Proposition 2 says
   that eventual coincidence at a point is an open condition, so dense
   eventual coincidence `~dc` is an equivalence relation, and that the
   generalized return vectors `GR(Phi)` form a subgroup. Proposition 1,
   assuming pure discrete spectrum, identifies
   `{v : T - v ~dc T}` with the union of `Lambda^k R`. The proposed group
   `H(T)` is that set. In these sources the premise "tilings sharing a tile
   are `~dc`" is obtained from pure discrete spectrum (Lemma 4.4) or
   inside the proof of Theorem 3.1; here it is the already compiled
   `hull_dense_eventual`.
2. Lee, Moody and Solomyak, *Consequences of pure point diffraction
   spectra for multiset substitution systems*,
   [arXiv:0910.4450](https://arxiv.org/abs/0910.4450), Theorem 4.7: for a
   repetitive primitive substitution tiling with Meyer return set `Xi(T)`,
   pure discreteness is equivalent to `dens(D_{Q^n x}) -> 1` for all
   `x in Xi(T)`, with `Xi(T)` the displacements between tiles of one type.
   This is the density form of the same return-vector condition; the cited
   Solomyak 1997 theorems (6.1, 6.2) were not opened and are relied on only
   through this paper and Akiyama–Lee.
3. Akiyama and Lee, *Algorithm for determining pure pointedness of
   self-affine tilings*, [arXiv:1003.2898](https://arxiv.org/abs/1003.2898),
   Theorems 2.5 and 3.4: overlap coincidence characterizes pure point
   spectrum, and a generating set of return vectors suffices.
4. Sirvent and Solomyak, *Pure discrete spectrum for one-dimensional
   substitution systems of Pisot type*,
   [DOI](https://doi.org/10.4153/CMB-2002-062-3), Theorem 3.1: return words
   enter the balanced-pair criterion through the splitting of the fixed
   word at occurrences of a prefix.

The argument is therefore standard. No novelty is claimed for it; the new
content is the Lean specialization to the literal family and its
combination with the repository's zero-fibre characterization.

## Hypotheses that transfer and those that do not

- Transfers: openness of eventual coincidence, transitivity through a
  tiling, translation equivariance and inflation equivariance are compiled
  generic lemmas. `hull_dense_eventual` is compiled for `k >= 2`.
- The return vectors must generate the whole length group `ell(Z^3)`. This
  is a property of the specific substitution. Here `00` occurs in the
  image of `2` and `11` in the image of `1` for `k >= 2`, and
  `ell(2) = beta ell(1) - ell(0) - k ell(1)`. No general theorem that
  return vectors generate the length group is used or claimed.
- Does not transfer: the nonunit boundary of BSW Proposition 3 and
  Corollary 3. For period doubling `GR(Phi) = Z` while the union of
  `Lambda^k R` is `Z[1/2]`; equality needs unit eigenvalues. The family
  has determinant two, so the result must not be stated as an
  identification of `H(T)`. Only the inclusion `ell(Z^3) <= H(T)` is
  proposed.
- Does not transfer: any conclusion about the maximal equicontinuous
  factor, coincidence rank on all fibres as a published invariant, or the
  measure-theoretic statements.

## Negative controls

- BSW Example 4.5 (table substitution): a return vector `v` of an
  admissible tiling for which the periodic pair `Q` and `Q - v` is nowhere
  eventually coincident. The premise "sharing a tile implies `~dc`" is
  therefore a real hypothesis and is kept as an explicit argument of the
  generic module.
- At `k = 1` the image of `1` is `012` and contains one tile of type `1`.
  The second tile used for the return vector `ell(1)` is absent; a Lean
  control records this, and no `k = 1` statement is made.
- The seam tiling and its inflation are distinct tilings over zero with
  different closed origin patches. The conclusion is a common tile and
  dense eventual coincidence, never equality or injectivity.

## Decision

Proceed. Implement the generic subgroup and the three inclusions, then the
family instantiation with the guard `k >= 2`. State the all-fibre
consequence only as dense eventual coincidence of tilings with equal
solenoid image. Keep coincidence rank one in the published sense,
almost-everywhere injectivity and the invariant-measure `L2` conclusion as
open formal obligations.
