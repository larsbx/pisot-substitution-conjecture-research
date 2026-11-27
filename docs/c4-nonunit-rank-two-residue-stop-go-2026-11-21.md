# Nonunit rank-two residue: fixed-tiling parity, source decision

## Target

[Theorem E](c4-nonunit-twin-endpoint-2026-11-21.md) leaves two cases at nonunit
determinant and coincidence rank two: a single-edge eventual range, and both endpoint maps
non-injective. Proposed step: the twin involution `ι` has no fixed point and commutes with
the inflation `Φ`, so it is a free involution of `Fix(Φⁿ)`. Count `Fix(Φⁿ)` and read the
parity.

## Sources and hypotheses

| Source | Consequence for this step |
| --- | --- |
| [Barge, *Factors of Pisot tiling spaces and the coincidence rank conjecture*, Lemmas 13–14, Theorem 17](https://arxiv.org/abs/1301.7094) | Twins are disjoint at every inflation level and `ι` commutes with `Φ`. The statements are quoted verbatim in the [trivial-stack note](c4-nonunit-trivial-stack-2026-11-21.md). The proof of Theorem 22 already counts periodic words at odd determinant. |
| [Barge–Diamond, *Cohomology of substitution tiling spaces*, Theorem 4](https://arxiv.org/abs/math/0702669) | `H¹(Ω; ℚ)` is the incidence part plus `H¹(ER; ℚ)`. So `#Fix(Φⁿ) = tr(Φⁿ* | H¹) − 1`. The count below is proved directly from words and does not import this. |
| [Anderson–Putnam, *Topological invariants for substitution tilings and their associated C\*-algebras*](https://doi.org/10.1017/S0143385798100457) | Periodic points of the inflation are counted on the complex. Standard. Not re-read this session; nothing is imported from it. |
| Repository: [even-residue note](c4-even-stack-residue-2026-11-19.md) | **Prior art in the repository.** Under a strict system it already derives `χ_M ≡ t³` and a grouped `K₂,₂`. Its covering argument uses the strict system only for `dim H¹(X) ≤ 4`. |
| Repository: [Theorem P+ and Theorem H3](c4-rank-two-wall-2026-11-16.md) | **Prior art in the repository.** Theorem H3 excludes rank two at `dim H¹ = 3` for every determinant. So the single-edge case is already excluded, and the residue list of the twin-endpoint note overstated it. Theorem P+ gives `r · q₁ | c_n` with `h_n r̄ = (t + 1) q̄₁`. With a trivial stack relation the divisibility would be an equality, and its trace is the parity proposed here. |

Hypotheses that transfer: PIP3, nonunit determinant, rank two, and the trivial stack
relation, which gives `ι` on `Ω` itself. Hypotheses that do not: at unit determinant `ι`
lives on the stack quotient, where the count of fixed tilings is not that of `σ`.

Controls. Thue–Morse has a free involution of `Fix(Φⁿ)` (the letter exchange) and an even
count for every `n`. Tribonacci has pure discrete spectrum and even counts for `n ≤ 3`, so
an even count detects nothing by itself.

## Decision

**Proceed, narrowed.** The parity is the trace of a condition the repository already has
in divisor form. It is not a new invariant. What is new is its combination with Theorem E
and Theorem H3 into a normal form for the residue, and the removal of the strict-system
hypothesis from the nilpotence of the even-residue note. Implement only the literal count and
the residue classification. Do not build a second divisor search. The single-edge case is
redirected to Theorem H3.
