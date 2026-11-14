# Parameter family stop/go — November 14, 2026

**Decision: redirect the proposed root-nullity search.** The family below is
primitive irreducible nonunit Pisot, but its parameters `k >= 2` already admit
short strong-coincidence witnesses using an existing repository argument.
The useful remaining candidate is finite actual forward reachability, subject
to a further identification check before new machinery is implemented.

This note records a feasibility and literature review. The displayed algebra
and word identities were hand-derived and independently checked by a second
agent. They were not Lean-compiled, tested by a new executable, or accepted as
new governed claims. The current named-termination acceptance remains separate.

## Proposed family and exact arithmetic

For an integer `k >= 1`, with ordinary word repetition, define

\[
\sigma_k(0)=1,\qquad\sigma_k(1)=0\,1^k\,2,\qquad\sigma_k(2)=001.
\]

The `k=1` member is the named fixture `1/012/001`. Its source-column incidence
matrix and square are

\[
M_k=\begin{pmatrix}0&1&2\\1&k&1\\0&1&0\end{pmatrix},\qquad
M_k^2=\begin{pmatrix}1&k+2&1\\k&k^2+2&k+2\\1&k&1\end{pmatrix}>0.
\]

Thus it is primitive. Its determinant is `2`, and its characteristic polynomial
is `f_k(x)=x^3-kx^2-2x-2`. The only possible rational roots are `±1, ±2`, with
values `-k-3`, `-k-1`, `2-4k`, `-4k-6`; none is zero. The cubic is irreducible.
Its discriminant is

\[
\Delta_k=-8k^3+4k^2-72k-76=-4(2k^3-k^2+18k+19)<0.
\]

There is one real root `beta_k`, greater than `2` because `f_k(2)<0`, and a
complex-conjugate pair. Their squared modulus is `2/beta_k<1` by Vieta.
This verifies the Pisot and nonunit conditions throughout the stated range.
The boundary `k=0` has its real root below `2`, so that boundary cannot inherit
the Pisot conclusion.

## Coincidence already has a short route

Put `A=0 1^k 2` and `B=001`. The complete second iterates are

\[
\sigma_k^2(0)=A,\quad \sigma_k^2(1)=1A^kB,\quad \sigma_k^2(2)=11A.
\]

For every `k >= 3`, their prefixes of length three are `011`, `101`, `110`.
All have Parikh vector `(1,2,0)`, and their next letter is `1`. Hence one
simultaneous three-letter prefix coincidence occurs at depth two.

For every `k >= 2`, including the boundary `k=2`, the following pairwise
witnesses suffice:

| Pair | Substitution depth | Equal-Parikh prefixes | Common next letter |
| --- | ---: | --- | ---: |
| `1,2` | 1 | empty / empty | 0 |
| `0,1` | 2 | `01` / `10` | 1 |
| `0,2` | 3 | `10` / `01` | 1 |

The last row uses `sigma_k^3(0)=sigma_k^2(1)` and
`sigma_k^3(2)=sigma_k^2(0) sigma_k^2(0) sigma_k^2(1)`: the same witness is
read inside the initial blocks. This includes literal word order and does
not extrapolate from finitely many parameters.

The mechanism is existing repository material:
`docs/p1a-a1-prime-2026-10-05.md`, §3c.2 **Lemma L_y**, proves the `xy/yx`
prefix witness when `sigma(x)=y`, `sigma(y)=x y^r c`, `r>=2`; §3c **Lemma T**
is the prefix-transfer argument. Their proofs specialize here even though
the complete F1/F2 family definitions do not. No novelty claim is made.

The existing formal consumer in `proof/PscVerif/PscVerif/StrictSystem.lean` is

```lean
theorem no_strictSystem_of_strongCoincidence {s : α → List α}
    (hw : ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c')
    (C : Finset (List α × List α)) : ¬ StrictSystem s C
```

Parameterizing the witnesses would therefore supply strict exclusion without
constructing a new inverse-overlap graph. The `k=1` base case has its own
historical accepted geometric proof; this note does not transfer that receipt
to the uncompiled family specialization.

## Proportional primary-source review

1. **Barge, Pure discrete spectrum for a class of one-dimensional substitution
   tiling systems**, [arXiv:1403.7826v2](https://arxiv.org/html/1403.7826v2),
   Theorem 3.13 and Remark 3.14. The theorem requires primitive Pisot inflation,
   injective initial letters, and constant or eventually constant final
   letters. These requirements cannot be replaced by a common suffix alone.

2. **Barge, The Pisot Conjecture for beta-substitutions**,
   [arXiv:1505.04408v2](https://arxiv.org/html/1505.04408v2), Theorem 15.
   The PDS result concerns the actual substitution arising from the
   beta-transformation. It does not cover every substitution having the same
   characteristic polynomial.

3. **Minervino and Thuswaldner, The geometry of non-unit Pisot substitutions**,
   [publisher PDF](https://www.numdam.org/item/10.5802/aif.2884.pdf),
   Definition 2.1, §8.2 and Theorem 9.10. Strong coincidence gives
   measure-disjoint subtiles in the nonunit representation; the stated tiling
   theorem also requires geometric property `(F)`. The actual prefix-tile and
   measure identifications must be proved before importing measure conclusions.
   Strong coincidence is not silently promoted to PDS.

4. **Barge, Štimac and Williams, Pure discrete spectrum in substitution tiling
   spaces**, [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf),
   §3, Theorem 3.2 and Corollary 2. Termination with coincidence includes finite
   irreducible-factor closure and productivity of every factor. For irreducible
   Pisot substitutions, one unequal-letter swap seed satisfying this complete
   condition suffices for tiling PDS. Finiteness remains a separate obligation.

## Prior coverage and conjugacy screen

The candidate is not literally one of the inspected catch-up-free A–D or
F1/F2 normal forms: its image `001` differs from their prescribed run-ending
words. In the determinant-two parity description, the odd letters are `0,2`,
and the proper prefix `00` has even parity; catch-up-free family conclusions
must not be assigned by resemblance. The November 4 forward/reversed run
families have different literal images and incidence polynomials. This screen
establishes no exhaustive nonconjugacy theorem.

The candidate's first- and last-letter maps are `(1,0,0)` and `(1,2,1)`.
Every positive power has image size two. Consequently powers, relabelling and
reversal do not directly satisfy the Barge endpoint condition; there is no
common nonempty prefix or suffix of the powered images for the standard
common-word rotation shortcut.

For `k>=2`, `f_k(k)<0<f_k(k+1)` and the finite greedy digit sequence of `1`
is `(k,2,2)`: the first remainder is `beta_k-k`, its next product is
`beta_k(beta_k-k)=2+2/beta_k`, and the remaining products give digit `2`
followed by zero remainder.
The standard beta-substitution is `0->0^k1, 1->002, 2->00`. No conjugacy of
the candidate to that substitution, including a return-substitution or other
recoding conjugacy, was established. Shared polynomial data supplies none.
Prior family coverage must be rechecked if such a map is found.

The companion `0->1, 1->02 1^k, 2->001` is a useful stopping control: every
image ends in `1`, so every inflated nonempty balanced pair has terminal diagonal
factor `(1,1)`. Its strict exclusion needs no new root-nullity machinery.

## Narrow next obligation and scope

**Stop the proposed new root-nullity search for this family.** Reuse the
short existing coincidence mechanism. Conditional on the remaining prior-art
and conjugacy screen, the precise further target is: for every `k>=2`, prove
finite actual `ChildNC` reachability from `([0,1],[1,0])`. A parameter-dependent
finite carrier and bound are sufficient. Its membership proof must include
the seed and every actual child, with ordered words and complete reduction.
No new census, fixed parameter sample or resource cap supplies this theorem.

The existing finite-productivity bridge can then combine finiteness with
strict exclusion. A spectral consequence would additionally retain the exact
published bridge and its hypotheses. This remains a family forward-closure
target; universal A1′, BH, C4, G1, #84 and PSC are unchanged. This note adds no executable implementation or governed status change;
merge decisions remain with the user.
