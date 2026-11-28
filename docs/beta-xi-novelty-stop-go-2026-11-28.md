# Novelty and transcendence routes for ξ_{k,m}: literature stop/go (2026-11-28)

Status: research-design decision with imported results; no new compiled result, no PSC claim, ledger entry, vendor pin or theorem status change.

## Proposed claim examined

For `k ≥ 1`, `m ≥ 4`, `β_m² = mβ_m + 1` and `w` the fixed word of `σ_k² = (1, 01^k2, 001)²` starting at `0`, the number `ξ_{k,m} = Σ_{n≥1} (w_n + 1) β_m^{-n}` is transcendental and is the unique expansion of itself over `{0, …, m}`. The question is whether either part is new, and which route to transcendence the repository should rely on.

## Sources (primary, read for this note)

1. [Adamczewski–Bugeaud, *Dynamics for β-shifts and Diophantine approximation*, ETDS 27 (2007)](https://doi.org/10.1017/S0143385707000223), [author manuscript](https://adamczewski.perso.math.cnrs.fr/AB_ETDS.pdf). Read from the manuscript text. **Corollary 1:** for `β` Pisot or Salem and `α ∈ [0,1]` algebraic, either the complexity of `d_β(α)` is bounded or `liminf p(n)/n = +∞`. Here `d_β(α)` is the β-expansion given by the β-transformation, that is, the greedy expansion. The paper notes that Corollaries 1 and 2 for Pisot `β` were already obtained in their Annals paper, by an argument depending on K. Schmidt (1980).
2. [Adamczewski–Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer bases*, Ann. of Math. 165 (2007)](https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf): the integer-base and Diophantine-exponent framework (Theorem AB: `Dio(a) > 1` gives `Σ a_k β^{-k} ∈ Q(β)` or transcendental, for `β` Pisot or Salem).
3. [Kebis–Luca–Ouaknine–Scoones–Worrell, *Transcendence for Pisot morphic words over an algebraic base*, arXiv:2405.05279](https://arxiv.org/abs/2405.05279), read from the arXiv HTML version 2.
   - Theorem 9: an echoing word `u` over `{0, …, b-1}` gives `Σ u_n β^{-n}` transcendental or in `Q(β)`, for every algebraic `β` with `|β| > 1`.
   - Echoing is unconditional for binary irreducible Pisot morphisms. For larger alphabets it holds assuming the Pisot conjecture; balanced-pair termination with coincidence is stated as sufficient.
   - The read text contains no unimodularity hypothesis. Only part of the paper was read verbatim; Theorems 7–14 beyond Theorem 9 were not.
4. K. Schmidt, *On periodic expansions of Pisot and Salem numbers*, Bull. London Math. Soc. 12 (1980), as recalled in source 1: for Pisot `β`, elements of `Q(β) ∩ [0,1)` have eventually periodic β-expansions. Not re-read; cited through source 1.
5. Repository: [family spectral closure](c4-family-spectral-closure-2026-11-14.md), where the literal σ_k has pure discrete spectrum for `k ≥ 1` by Barge–Štimac–Williams Corollary 2 (an external theorem; no unimodularity needed). Also the [Komornik–Loreti constant](https://mathworld.wolfram.com/Komornik-LoretiConstant.html), transcendental (Allouche–Cosnard 2000), as the standard example in the unique-expansion literature.

## Hypotheses: what transfers

| Route | Hypotheses | Status here |
| --- | --- | --- |
| A: AB Corollary 1 | `β` Pisot; `α ∈ [0,1]`; greedy expansion; not eventually periodic; `p(n) = O(n)` | all compiled: `pisot_facts`, `xi_inputs`, `xi_complexity_unbounded` |
| B: KLOSW Theorem 9 + Schmidt | `w` echoing; then `ξ ∉ Q(β_m)` | echoing needs KLOSW's balanced-pair-with-coincidence notion for σ_k (or σ_k²). The repository's termination is in Barge–Štimac–Williams' full-factor sense for the swap seed; whether the two notions coincide is **not checked**. `ξ ∉ Q(β_m)` is formalizable here (below). |

Route B, if its transfer gap closes, gives more than route A for the plain sum `Σ w_n β^{-n}`. It yields the `Q(β)`/transcendental dichotomy for every algebraic `β` with `|β| > 1`, not only Pisot bases with greedy digits. The coding `w ↦ w + 1` changes the sum by `1/(β - 1) ∈ Q(β)`, so the dichotomy transfers to `ξ_{k,m}`.

## Prior art and novelty

- Transcendence of a number whose greedy β-expansion, in a Pisot base, is non-eventually-periodic with linear complexity is a direct consequence of source 1. Fixed points of primitive substitutions and their letter-to-letter codings have linear complexity. So transcendence of `ξ_{k,m}` is an **instance**, not a new theorem.
- Unique expansions with transcendental value are classical (Komornik–Loreti). In metallic bases with `m ≥ 4` every stream of interior digits is unique, so uniqueness of `ξ_{k,m}` is cheap and not new.
- The specific family has no literature presence found, but that is not a novelty a paper could claim: the construction is a formal specialization of known theorems.

## Negative controls / counterexamples

- A periodic word gives an element of `Q(β)` (route B's other alternative), so non-periodicity is essential.
- For non-Pisot, non-Salem `β`, elements of `Q(β)` can have non-eventually-periodic expansions (source 1, citing Schmidt). So route B's `Q(β)` exclusion via periodicity needs `β` Pisot or Salem.
- Greedy and unique differ: the golden coding is greedy but not unique (`code_not_unique`).

## Decision

- **Stop** any novelty claim for the transcendence or uniqueness of `ξ_{k,m}`; record them as specializations.
- **Proceed** with one narrowed formal target: the quadratic Pisot case of Schmidt's theorem for metallic bases. Elements of `Q(β_m) ∩ [0,1)` have eventually periodic greedy expansions, hence `ξ_{k,m} ∉ Q(β_m)` and `ξ_{k,m}` is irrational, unconditionally and in Lean. That closes the internal half of route B and gives an independent irrationality proof.
- **Defer** the KLOSW echoing transfer: comparing balanced-pair notions is a separate stop/go question.
