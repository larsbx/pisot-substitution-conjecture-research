# Actual balanced cuts approaching the original prefix tiles

Decision on 2026-11-12 (America/New_York): **proceed with literal prefix
embedding, exact residue agreement, and uniform stable-coordinate error;
retain the counting-to-positive-measure step as a separate obligation.**
Baseline: `main@9a1357ed5dae3b4502d29c34396d0e9403ccca75`.
This decision is recorded before new theorem-facing implementation.

## Proposed claim

For a finite source word `u`, an actual marked position of `sigma^k(u)`,
and a reference occurrence of its parent letter in the same authenticated
infinite word `w`, construct the corresponding actual prefix point `y` of
`w` with the same following letter. If `x` is the Parikh vector before the
marked output position, prove the exact identity

\[
 x^*-y=A^k z^*,\qquad
 z=p(u_{<i})-p(w_{<j}).
\]

The complete parent ordinal, local mark, following letter, and signs must
be retained. A finite set of source-prefix corrections suffices for all
inflation depths and all output positions. For the two original named
words and `k=12n`, use the already proved fixed-word identities, original
matrix-adic factor, and `7/8` block contraction to obtain a uniform error
bound tending to zero. At every residue depth `q<=k`, the two points have
exactly equal residues. Applying the construction to the two actual marks
of a balanced cut gives approximation to both corresponding tiles.

This is the previously written embedding step of Theorem M1 in
[the compact counting bridge](c4-nonunit-madic-counting-bridge-2026-11-04.md),
Section 4. It does not itself prove that the intersection has positive
product-Haar measure.

## Primary sources checked

1. Minervino and Thuswaldner, [*The geometry of non-unit Pisot
   substitutions*](https://arxiv.org/pdf/1402.2002), Sections 4 and 7,
   especially Lemma 7.5, Theorem 7.7, and Lemma 3.1. Literal prefix
   automata and contracting internal images supply the established
   construction. Their representation includes finite places. We retain
   the repository's explicitly constructed `H_M`; no identification with
   their localized representation, tiling property, or positivity theorem
   is imported.
2. Thuswaldner, [*Unimodular Pisot substitutions and their associated
   tiles*](https://www.numdam.org/item/JTNB_2006__18_2_487_0.pdf), Section
   4.3, printed page 517. Switching between prefix and suffix conventions
   changes translations and signs. Our identities are derived from actual
   positive-prefix words, not transferred from the paper's signed tile
   convention. Its unimodularity and later super-coincidence assumptions
   do not apply to the determinant-two examples.
3. Moody, [*Uniform Distribution in Model Sets*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/2304DD08EC0AD970DEF94D7C180C4752/S0008439500015630a.pdf/div-class-title-uniform-distribution-in-model-sets-div.pdf),
   Proposition 1 and Theorem 1, pages 125-127. The fixed-parameter density
   statement for regular windows must be distinguished from the
   almost-sure statement for arbitrary measurable windows. Approaching
   compact intersections is the input to a later regular-cover argument;
   proximity is not a density or positive-measure theorem.

The repository side-notes ledger and existing prefix, residue, strict-cut,
and archived-consumer modules were inspected. The ongoing ordinary-ancestry
composition work is independent and is not a dependency of this increment.

## Transferred hypotheses and controls

- A reference point must be an actual occurrence in the same word. The
  two named sources have equal incidence but distinct infinite words.
- Use only genuine fixed-prefix powers. Both named words are period two;
  a one-step fixed-word identity is false. Multiples of twelve are an
  authenticated cofinal sequence with a proved contraction constant.
- The correction can be nonzero. Exact residue agreement through depth
  `k` does not identify the points in the full inverse limit or in the
  stable factor, nor does it guarantee agreement at depth `k+1`.
- The finite correction set is fixed by the uninflated source and its
  reference occurrences. Allowing source corrections to grow with depth
  would invalidate the uniform convergence argument.
- The two following letters at a strict balanced cut are distinct by the
  existing `StrictSystem.cut_follow` theorem. Nearness to both compact
  tiles must not be described as membership in their intersection.
- Canonical executable checks belong in Mojo; an independently written
  Python oracle may compare literal witnesses. Finite replay does not
  establish the universal quantified Lean theorem.

## Scope decision

Proceed with the formal specialization of this standard prefix-embedding
argument and exact witness replay. Preserve the fixed-origin regular-window
count, positive cut density, outer regularity, and their analytic assembly
as separate obligations wherever not proved. Do not promote general C4,
PSC, all-packet coverage, or a positive overlap from this increment.
