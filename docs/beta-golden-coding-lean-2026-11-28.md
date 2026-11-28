# Golden-ratio block coding of the σ_k² fixed word in Lean (2026-11-28)

Status: compiled Lean results for the literal family. The transcendence conclusion is the external Adamczewski–Bugeaud implication, not formalized. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Source decision: [beta-numeration research route](beta-numeration-research-route-2026-11-27.md), the bullet "At phi, use constant-width injective blocks". Builds on the [golden endpoint theorem](beta-golden-endpoint-lean-2026-11-27.md) and the [complexity note](beta-family-complexity-lean-2026-11-27.md).

## Assumptions and hypotheses

Module [`PscVerif.BetaGoldenCoding`](../proof/PscVerif/PscVerif/BetaGoldenCoding.lean). `code k n = block (w_{⌊n/4⌋}) (n mod 4)` with `0 ↦ 0000`, `1 ↦ 0010`, `2 ↦ 0100`; `w` is the fixed word of `σ_k²`, `k ≥ 1` where stated. Values use the golden module's `value` over `Bool`.

## Statement

| Declaration | Content |
| --- | --- |
| `psum_le`, `value_le_one` | a no-`11` stream has partial sums `≤ 1 - φ^{-(N+1)}` and value `≤ 1` |
| `tail_lt_one` | a no-`11` stream with a `00` somewhere has value `< 1` |
| `code_no_one_one`, `code_zero_zero` | `c` has no `11`, and `00` occurs at or after every position |
| `code_greedy` | every remainder of `c` is in `[0,1)` and every digit is `⌊φ · remainder⌋` |
| `code_not_eventuallyPeriodic` | `k ≥ 1`: `c` is not eventually periodic |
| `code_factors_linear` | `k ≥ 1`: at most `108 (k²+2)² (⌊n/4⌋ + 2)` factors of length `n` |
| `code_complexity_unbounded` | `k ≥ 1`: the factor counts of `c` are unbounded |
| `code_not_unique` | `k ≥ 1`: `c` is not the unique expansion of its value |
| `golden_pisot` | `1 < φ`, `φ² = φ+1`, `(1-φ)² = (1-φ)+1`, `|1-φ| < 1` |

## Derivation / reduction

1. `psum_le` by strong induction on `N`. A leading `0` gives `r · (1 - r^{N+1}) ≤ 1 - r^{N+2}`. A leading `1` is followed by `0` and gives `r + r² (1 - r^{N}) = 1 - r^{N+2}`, using `r² + r = 1`.
2. `value_le_one` from step 1 and `Real.tsum_le_of_sum_range_le`.
3. `tail_lt_one`: with `00` at `j`, `value = psum j + r^j · r² · value(tail) ≤ 1 - r^{j+1} + r^{j+2} = 1 - r^j (r - r²) < 1`.
4. Every block starts and ends with `0` and has no internal `11`, so `c` has no `11`. Every block has `00` at offset `0` or `2`, so step 3 applies to every tail. As in the metallic case, `φ R_{n-1} = c_n + R_n` with `R_n ∈ [0,1)` gives the floor identity.
5. A period `p` of `c` is a period `4p` of `c`, and the middle digits of a block decode its letter (`decode_code`). So `w` would be eventually periodic, contradicting `word_not_eventuallyPeriodic`.
6. A factor of `c` of length `n` at `s` is determined by the factor of `w` of length `⌊n/4⌋ + 2` at `⌊s/4⌋` and the offset `s mod 4` (`factor_code`). The count is at most `4 · 27 (k²+2)² (⌊n/4⌋ + 2)`.
7. `c 0 = 0` and `c 6 = 1` (since `w 1 = 1`), so `c` is not constant; by `isUnique_iff` it is not unique.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The module is in the root import closure. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Negative controls

- `(10)^∞` is no-`11` with value exactly `1` (`value_alternating` of the golden module shifted by one digit). `tail_lt_one` therefore needs a `00`; `value_le_one` alone is not strict.
- `code_not_unique` is the route note's warning made formal: greedy is a selection, not global uniqueness.

## Non-claims / remaining gaps

- Transcendence of `value c` rests on Adamczewski–Bugeaud Corollary 1, not formalized.
- Novelty is not addressed.
