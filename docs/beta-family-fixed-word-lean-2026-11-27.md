# Fixed word of σ_k² and non-eventual periodicity in Lean (2026-11-27)

Status: compiled Lean result for the literal family. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Source decision: [beta-numeration research route](beta-numeration-research-route-2026-11-27.md), section "PSC application", first two obligations (fixed word bound to literal iterates; non-eventual periodicity) and the transfer by `a ↦ a+1`. Builds on the [metallic unique-expansion theorem](beta-metallic-unique-lean-2026-11-27.md).

## Assumptions and hypotheses

Module [`PscVerif.BetaFamilyFixedWord`](../proof/PscVerif/PscVerif/BetaFamilyFixedWord.lean). The substitution is the existing literal `Psc.ParameterFamilyRows.substitution k`: `0 ↦ 1`, `1 ↦ 0 1^k 2`, `2 ↦ 001`. The word is the existing generic limit `Psc.FixedPointLimit.limit` of the chain `σ_k^{2n}(0)`; nothing is re-implemented. Non-periodicity uses `k ≥ 1` (irreducibility of the characteristic polynomial, `Psc.ParameterFamilyPisot.irreducible`), weaker than the route note's `k ≥ 2`.

`EventuallyPeriodic x` means `∃ N p, 0 < p ∧ ∀ i ≥ N, x (i + p) = x i`.

## Statement

| Declaration | Content |
| --- | --- |
| `word_zero` | `w 0 = 0` |
| `word_prefix` | the length-`|σ^{2n}(0)|` prefix of `w` is literally `σ^{2n}(0)` |
| `word_fixed` | `σ²` of any prefix of `w` is the prefix of `w` of the image length |
| `word_not_eventuallyPeriodic` | `k ≥ 1 → ¬ EventuallyPeriodic w` |
| `det_pow_sub_one_ne_zero` | `k ≥ 1, N ≥ 1 → det (M^N - 1) ≠ 0`, `M` the rational incidence matrix |
| `shifted_not_eventuallyPeriodic` | the same for `w + 1` over `{0, …, m}`, `m ≥ 3` |
| `xi_unique` | `m ≥ 4`, any base `β² = mβ + 1`: `w + 1` is the unique expansion of its value `ξ_{k,m}`, `β⁻¹ < ξ_{k,m} < 1`, and the stream is not eventually periodic |

## Derivation / reduction

1. `σ_k²(0) = 0 1^k 2`, so `[0]` is a prefix of its image and the image is longer. The existing `grow_of_nonerasing` and `limit` give `w`, and `ofFn_limit_of_prefix` and `limit_fixed_eq` give `word_prefix` and `word_fixed`.
2. Suppose `w (i+p) = w i` for `i ≥ N`. The letter counts of the window `[L, L+p)` do not change as `L` moves past `N`, because the letter leaving is the letter entering (`window_const`). Call them `q`.
3. Take a nonzero integer `y` with `y·q = 0` (`exists_orthogonal`). Then `g(L) = Σ_a y_a |w[0,L)|_a` satisfies `g(L+p) = g(L)` for `L ≥ N`, so `g` is bounded (`bounded_of_periodic`).
4. On `L = |σ^{2n}(0)|`, step 1 and `count_iterate_subst` give `g(L) = yᵀ M^{2n} e₀`. So `a_n = yᵀ M^{2n} e₀` is a bounded integer sequence.
5. Pigeonhole on `(a_n, a_{n+1}, a_{n+2})` gives `n < n'` with equal triples. Columns `e₀`, `M²e₀ = (1,k,1)` and `M⁴e₀ = (k²+2k+2, k³+4k+2, k²+2)` are independent (determinant `-(2k+2)`), so `yᵀM^{2n} = yᵀM^{2n'}` (`samples_determine`). Since `det M = 2`, `M^{2n}` is invertible and `yᵀ(M^{2T} - 1) = 0` with `T = n' - n ≥ 1`.
6. `det(M^N - 1) ≠ 0` for `N ≥ 1`. If the irreducible `χ_M` divides `X^N - 1`, Cayley–Hamilton gives `M^N = 1`, so `2^N = 1`. Otherwise `χ_M` and `X^N - 1` are coprime, and evaluating a Bézout identity at `M` inverts `M^N - 1`. This contradicts step 5.
7. `a ↦ a+1` is injective, so `w+1` is not eventually periodic. For `m ≥ 4` its digits lie in `{1,2,3} ⊆ {1, …, m-1}`, and `Base.interior` gives uniqueness and the interval.

The argument uses no letter frequencies, Perron–Frobenius limit, or Pisot hypothesis: only irreducibility and `det M = 2`.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The module is in the root import closure. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Negative controls

- Step 6 is where the hypotheses bite. `0 ↦ 010`, `1 ↦ 101` has incidence `[[2,1],[1,2]]` with eigenvalue `1`, so `det(M - 1) = 0`, and its fixed word `(01)^∞` is periodic. The argument correctly stops there.
- Uniqueness of `ξ_{k,m}` needs `m ≥ 4`. At `m = 3` the digit `3 = m` occurs after interior digits, so `EndpointsInitial` fails and `Base.isUnique_iff` gives a second expansion.

## Non-claims / remaining gaps

- No factor-complexity bound, linear or otherwise. That is the next obligation, and the one Adamczewski–Bugeaud Corollary 1 needs.
- No greedy admissibility for `w + 1` in base `β_m`, and no Pisot hypothesis for `β_m` stated in Lean. Both are inputs to the external theorem, which is not formalized.
- No transcendence statement and no novelty claim for `ξ_{k,m}`.
- The golden-ratio block coding `0 ↦ 0000, 1 ↦ 0010, 2 ↦ 0100` is not treated.
