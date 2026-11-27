# Beta-numeration research route and literature stop/go (2026-11-27)

Status: research design, written mathematical reductions and imported results; no new compiled Lean result, executable acceptance, or promotion of PSC claims.

## Decision

Stop treating unrestricted uniqueness at the golden ratio as an open problem. Proceed with formal certification, the countable/continuum multiplicity boundary, and applications to explicit substitution languages. Keep recognizability of tilings, unique numerical valuation, and ordinary integer-base normality separate.

## Golden-base classification

For beta=phi, digits {0,1}, valuation pi(d)=sum_{n>=1} d_n phi^{-n}, the representable interval is [0,phi]. Only the endpoint streams are unique (only zero on [0,1)). This is known: [Glendinning and Sidorov, Unique representations of real numbers in non-integer bases (2001)](https://archive.intlpress.com/site/pub/files/_fulltext/journals/mrl/2001/0008/0004/MRL-2001-0008-0004-a012.pdf).

Direct derivation: phi^2=phi+1 makes 100 and 011 interchangeable. A unique nonconstant stream must avoid both patterns, hence alternate after its first change of digit. The suffix (01)^infinity equals 1000... by the geometric-series identity, and can be replaced. The constant streams are unique by nonnegativity and its reflected version. The two equal-value alternating/terminating tails both avoid 11: the greedy language on [0,1) requires every suffix to be lexicographically strictly below (10)^infinity. Do not confuse a selected greedy representative with uniqueness among all expansions.

For 0<x<1, the classical Sidorov–Vershik classification gives countably infinitely many expansions iff x lies in Z[phi] (equivalently a nonzero fractional part of n phi); all other x in that interval have continuum many. See [Ge and Tan, Numbers with countable expansions in base of generalized golden ratios](https://arxiv.org/abs/1504.01704), which recalls that result and treats alphabet-dependent generalized golden-ratio thresholds, distinct from the metallic family below. Formalizing the multiplicity statement requires more than finding one collision or a finite-prefix count.

## Uniform quadratic family

Let beta_m be the positive root of beta^2=m beta+1, m>=1, with full alphabet {0,...,m}. Set B={1,...,m-1}. For a stream d write R_n=pi(d_{n+1},d_{n+2},...). The full interval [0,m/(beta-1)] is covered by the first-digit intervals: consecutive intervals overlap because m/(beta-1)>1, and recursively choosing digits gives a bounded remainder and convergent valuation. An alternative first differing digit exists precisely when its shifted remainder lies in this full interval. Thus uniqueness iff, for every n, d_n<m implies R_n<1, and d_n>0 implies R_n>1/beta.

A positive digit cannot be followed by zero: R_{n+1}<1 at that zero contradicts R_n>1/beta. Reflection excludes an m after any digit below m. Endpoint digits therefore occur only in an initial constant run; after leaving it all digits are interior. Interior-only tails have values between 1/(beta-1) and (m-1)/(beta-1), strictly inside (1/beta,1) when m>=2. Initial zero or m runs obey the respective one-sided inequalities by geometric bounds. Constant endpoints are unique. Hence the complete streams are 0^infinity, m^infinity, or 0^r B^N or m^r B^N for r>=0. For m=1, B is empty. On [0,1), only zero and the zero-prefixed interior streams occur: an initial m with an interior tail has value > (m+1/beta)/beta=1. For m=2 this is a countable set, for m>=3 uncountable. This is a specialization to formalize, not a novelty claim.

The [shared exact quadratic carry contract](https://github.com/larsbx/finite-math-kernels/blob/main/docs/beta-numeration-carry-contract-2026-11-27.md) records the seven-state all-m equality criterion, integer transition and infinite acceptance. General Pisot finite-state normalization is prior art; [Frougny](https://fpsac-archive.github.io/FPSAC93/ARTICLES/Frougny.pdf). For constraints presented by a finite labeled graph, search the product with the equality carrier and sticky divergence for an infinite path (reachable cycle after divergence for unrestricted graph-path acceptance), replay actual labeled witnesses. Finite-prefix acceptance alone is not an infinite-word proof. For substitution hulls a finite graph of observed factors need not present the actual language: establish the appropriate correspondence or use only its justified one-sided implications.

## PSC application: uniquely representable transcendental candidates

For the existing literal substitution sigma_k=(1,01^k2,001), k>=2, use the one-sided fixed word w of sigma_k^2 beginning at 0. For m>=4 define xi_{k,m}=sum_{n>=1}(w_n+1) beta_m^{-n}. Its digits lie in {1,2,3} within B; the classification above gives uniqueness and a value in (0,1). The following are proof obligations, not newly certified results:
- Construct the actual infinite fixed word and bind its finite prefixes to literal iterates.
- Prove non-eventual periodicity and a linear factor-complexity bound; transfer both by the injective coding a->a+1.
- Prove greedy admissibility and the beta_m Pisot hypotheses; invoke [Adamczewski–Bugeaud, Dynamics for beta-shifts and Diophantine approximation, Corollary 1 (2007)](https://doi.org/10.1017/S0143385707000223): for an algebraic value in [0,1] in a Pisot/Salem base, greedy complexity is bounded or its ratio to length has liminf infinity. Non-eventual periodicity rules out bounded complexity; linear complexity rules out the other case. See [author manuscript](https://adamczewski.perso.math.cnrs.fr/AB_ETDS.pdf).
- At phi, use constant-width injective blocks 0->0000, 1->0010, 2->0100. No adjacent ones and recurring 00 give greedy admissibility; prove the coding preserves non-eventual periodicity and linear complexity. This produces a canonical transcendence candidate, never a globally unique phi expansion.
- Establish whether any resulting family is novel separately. Neither a pure discrete spectral theorem nor a finite factor census supplies these missing word-level hypotheses.

## Repository correspondence and acceptance

Existing source anchors at inspected revision 8bf2a627913bb7a9eb2f05b0ed3f08c54dc647d7:
- [numeration_addition](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bf2a627913bb7a9eb2f05b0ed3f08c54dc647d7/kernel/psc/numeration_addition.mojo), [numeration_conversion](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bf2a627913bb7a9eb2f05b0ed3f08c54dc647d7/kernel/psc/numeration_conversion.mojo), [pisot_state](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bf2a627913bb7a9eb2f05b0ed3f08c54dc647d7/kernel/psc/pisot_state.mojo) use exact integer states for substitution-position numeration. They do not prove fractional greedy admissibility; the conversion module explicitly separates it.
- [C4FiniteTileAutomaton](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bf2a627913bb7a9eb2f05b0ed3f08c54dc647d7/proof/PscVerif/PscVerif/C4FiniteTileAutomaton.lean) supplies a replay precedent, not the valuation theorem.
- [C4ParameterFamilyPisot](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bf2a627913bb7a9eb2f05b0ed3f08c54dc647d7/proof/PscVerif/PscVerif/C4ParameterFamilyPisot.lean) supplies family arithmetic, not the fixed-word complexity bridge.
- [Golden-ratio statistics/counting companion](https://github.com/larsbx/golden-ratio-normality-research/blob/main/docs/beta-numeration-statistics-2026-11-27.md).

First deliver the Lean endpoint theorem and the upstream carry semantics; then integrate pinned Mojo implementation and independent oracle, exact path witnesses and negative controls; then multiplicity and actual substitution word applications. Negative controls: 100/011; 1000.../(01)^infinity; finite factor samples masquerading as a hull; arbitrary equality graph mistaken for a greedy language; a periodic word mistaken for a transcendence witness. Future replay must follow tools/verify_all.sh and source-bound Lean/Mojo acceptance; no local gates executed for this note. Do not edit generated claim ledgers, vendor pins, or change PSC theorem status on the strength of this design note.
