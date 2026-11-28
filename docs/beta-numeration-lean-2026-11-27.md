# Beta-numeration obligations in Lean (2026-11-27)

Status: Lean formalization of the proof obligations listed under "PSC application" in the [research route](beta-numeration-research-route-2026-11-27.md). Acceptance is the focused gate `tools/check_beta_numeration.sh` (workflow `beta-numeration-lean.yml`) plus the unchanged full proof-bank audit. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending. No novelty is claimed: every mathematical statement here is a specialization of known results.

## Imported input

Adamczewski–Bugeaud, *Dynamics for β-shifts and some Diophantine approximation problems*, ETDS 27 (2007), Corollary 1: for a Pisot or Salem base `β` and algebraic `α ∈ [0,1]`, the complexity of the Rényi `β`-expansion of `α` is bounded or has `liminf p(n)/n = +∞`. It enters as the `Prop` `Psc.BetaNumeration.ABCorollary1` (restricted to Pisot bases), a hypothesis of the transcendence theorems, never an axiom. The audit rejects any axiom beyond `propext`, `Classical.choice`, `Quot.sound`.

## Modules and endpoints

| Module | Endpoint | Content |
| --- | --- | --- |
| `WordComplexity` | `eventuallyPeriodic_of_complexity_succ_le`, `succ_le_complexity` | Morse–Hedlund direction used: not eventually periodic ⇒ `p(n) ≥ n+1` |
| | `complexity_comp`, `EventuallyPeriodic.of_comp` | injective letter codings preserve complexity and reflect eventual periodicity |
| | `window_flatten` | a short window of `w₀w₁⋯` lies in some `w_t w_{t+1}` |
| `BetaNumeration` | `renyiExpansion_value` | greedy binding: a stream whose tail values are all `< 1` is the Rényi expansion of its value |
| | `isUnique_of_tails` | uniqueness criterion (sufficient direction), quantified over all bounded streams |
| | `transcendental_of_greedy` | greedy + not eventually periodic + `p(n) ≤ Cn` infinitely often ⇒ transcendental, given `ABCorollary1` |
| `BetaMetallic` | `beta_sq`, `top_sub_one`, `isPisot`, `beta_one` | `β_m² = mβ_m + 1`, `m/(β_m−1) − 1 = β_m⁻¹`, Pisot via conjugate `−β_m⁻¹`, `β_1 = φ` |
| | `isUnique_of_low`, `isUnique_interior` | for `m ≥ 2`: `0^∞`, every `0^r B^ℕ` and every `B^ℕ` (`B = {1,…,m−1}`) is uniquely represented |
| | `interior_value_mem`, `interior_renyi` | interior values lie in `(β⁻¹, 1)` and interior streams are greedy |
| `C4FamilyFixedWord` | `fixedWord_eq`, `block_eq` | the fixed word of `σ_k²` from `0`, bound to the literal iterates `τʲ(0)` |
| | `not_eventuallyPeriodic` | for `k ≥ 1` |
| | `frequently_linear` | `p(n) ≤ 12(k²+2k+4)n` for infinitely many `n` |
| `C4FamilyBetaTranscendence` | `xi_isUnique`, `xi_mem`, `renyi_xi` | `ξ_{k,m}` for `k ≥ 1`, `m ≥ 4`: unique expansion, value in `(β⁻¹,1)`, greedy |
| | `xi_transcendental` | `ABCorollary1 → Transcendental ℚ ξ_{k,m}` |

## How the two word-level obligations are discharged

**Aperiodicity** uses no frequency limit. If the fixed word were eventually periodic with period `p`, the discrepancy `p·|u_{[0,N)}|_a − N c_a` would take finitely many values. Along `N = |τʲ(0)|` the Parikh vectors are columns `A^j e₀` of `A = M_σ²`, and `A³ = (k²+4)A² + (4k−4)A + 4` is checked entrywise (`charpoly_identity`). Pigeonhole on consecutive triples makes the difference vectors `A^t v` parallel to the period vector `c`. Either `v = 0`, so two prefix lengths coincide against strict growth, or `A v = μ v` with `μ ∈ ℚ`, a rational root of `x³ − (k²+4)x² − (4k−4)x − 4`; the rational-root theorem leaves `±1, ±2, ±4`, and each value is a nonzero polynomial in `k ≥ 1` (`no_rational_root`).

**Linear complexity** is only needed along a subsequence, because Corollary 1's alternative is `liminf p(n)/n = ∞`. At `n = min_a |τ^{j+1}(a)|` each factor lies across two consecutive blocks `τ^{j+1}(a) τ^{j+1}(b)` of a long prefix, and `max_a |τ^{j+1}(a)| ≤ (k²+2k+4) n` because every letter occurs in every `τ(a)` (`len_le`).

**Greedy admissibility** at `β_m` needs no separate argument: every tail of a stream with digits `≤ m−1` has value `≤ (m−1)/(β_m−1) < 1` (`value_lt_one_of_low`), which is exactly the condition of `renyiExpansion_value`. Uniqueness implies the same through representability, but that direction is not needed here.

## Not formalized here

- The necessity direction of the uniqueness criterion, hence the full classification (that unique streams are *only* `0^∞`, `m^∞`, `0^r B^ℕ`, `m^r B^ℕ`), and the countable/continuum multiplicity boundary.
- The golden-ratio block coding `0→0000, 1→0010, 2→0100`. Its greedy admissibility is not a pointwise domination by a periodic stream of value `< 1` (the offset-1 dominating tail `(1100)^∞` has value `> 1`), so it needs the no-`11`/recurring-`00` Parry argument.
- The upstream seven-state carry contract and its Mojo binding.
- Corollary 1 itself.
