# Source review for the period of a strict C4 carrier

The proposed restriction for [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461) is that a supplied finite, completely strict, strongly connected ternary PIP carrier is primitive after track-swap normalization. Track order can still retain period two. This review precedes the new certificate controls.

| Source | Applicable argument and hypothesis boundary |
| --- | --- |
| [Seneta, Non-negative Matrices and Markov Chains](https://doi.org/10.1007/0-387-32792-4) | The cyclic classes of a finite irreducible incidence graph advance by one under every edge. This requires complete strongly connected support. |
| [Sirvent–Solomyak, Lemma 5.5 and Theorem 5.6](https://doi.org/10.4153/CMB-2002-062-3) | Rationally independent widths identify common vertices with balanced cuts. For the transfer between repeated occurrences here, the same integer relative prefix vector gives a more direct argument, even with dependent widths. |
| [Akiyama–Lee](https://arxiv.org/abs/1003.2898) | Overlap graph edges are supplied by actual child occurrences. We use that transport inside one repeated overlap, without equating the carrier to a graph of all hull overlaps. |
| [Barge–Diamond, Theorem 1](https://doi.org/10.24033/bsmf.2433) | A genuinely coincident pair exists in the Pisot setting. Reversal gives the corresponding right-end input. The proof needs actual coincident prefixes when the first-letter map fixes one letter and transposes the other two. |

The repository already supplies [enclosure](c4-overlap-carrier-enclosure-2026-11-04.md),
[ordered overlap sinks](c4-oriented-alignment-2026-11-04.md) and
[the first-factor reduction to fixed rays](c4-periodic-ray-decision-2026-11-14.md).
Earlier [phase-wise Parikh constraints](c4-periodic-parikh-phase-rigidity-2026-11-04.md)
allow imprimitive synthetic matrices. They do not provide literal realizations
and are not counterexamples to a word-level period restriction.

**Decision.** Proceed with synchronizing each repeated overlap inside two
actual ordered parent states, then apply the endpoint classification and the
literal good-edge witness to the sole two-cycle of distinct unordered pairs.
Keep a real reducible control with a nonconstant endpoint-pair cycle even
though its normalized child graph is primitive. Keep another with ordered
period two, to distinguish ordered and normalized graph claims. The proof
does not assume an a priori bound on component size or general G1 extraction.
