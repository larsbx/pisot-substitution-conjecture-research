# Linear complexity and the Adamczewski–Bugeaud inputs for ξ_{k,m} in Lean (2026-11-27)

Status: compiled Lean results for the literal family. The transcendence conclusion is an external published implication, not formalized. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Source decision: [beta-numeration research route](beta-numeration-research-route-2026-11-27.md), section "PSC application", remaining word-level obligations. Builds on the [fixed word and non-periodicity](beta-family-fixed-word-lean-2026-11-27.md) and the [metallic unique-expansion theorem](beta-metallic-unique-lean-2026-11-27.md).

## Assumptions and hypotheses

Modules [`PscVerif.BetaFamilyComplexity`](../proof/PscVerif/PscVerif/BetaFamilyComplexity.lean), [`PscVerif.BetaFamilyXi`](../proof/PscVerif/PscVerif/BetaFamilyXi.lean) and [`PscVerif.BetaFactorBounded`](../proof/PscVerif/PscVerif/BetaFactorBounded.lean). `k ≥ 1`. `factor x s n` is the list `x_s … x_{s+n-1}`; `factors x n` is the set of all of them. `ξ_{k,m} = B.value (w + 1)` for a `Base m` (`m r + r² = 1`, `r = β⁻¹`) with `m ≥ 4`.

## Statement

| Declaration | Content |
| --- | --- |
| `factors_finite_and_linear` | `n ≥ 1 →` `factors w n` is finite with at most `27 (k²+2)² n` elements |
| `shifted_factors_linear` | the same bound for `w + 1` |
| `pisot_facts` | `β = r⁻¹ > 1`, `β² = mβ + 1`, `(-r)² = m(-r) + 1`, `|-r| < 1`, `β + (-r) = m`, `β(-r) = -1` |
| `greedy` | every remainder of `w + 1` is in `[0,1)` and every digit is `⌊β · remainder⌋` |
| `xi_inputs` | uniqueness, `β⁻¹ < ξ < 1`, greedy digits, not eventually periodic, linear complexity |
| `eventuallyPeriodic_of_bounded` | any sequence whose factor sets are finite of bounded size is eventually periodic (Morse–Hedlund, the direction used) |
| `xi_complexity_unbounded` | the factor counts of `w + 1` are unbounded |

## Derivation / reduction

Complexity:

1. `ℓ_J(a) = |σ^{2J}(a)|` satisfies `ℓ_{J+1}(a) = Σ_c (M²)_{c a} ℓ_J(c)` (`blockLen_succ`, from the Parikh identity).
2. Every entry of `M² = [[1,k+2,1],[k,k²+2,k+2],[1,k,1]]` lies in `[1, k²+2]` for `k ≥ 1`. With `S_J = Σ_a ℓ_J(a)` this gives `S_J ≤ ℓ_{J+1}(a) ≤ (k²+2) S_J` and `S_{J+1} ≤ 3(k²+2) S_J`.
3. `σ^{2J}` maps each prefix of `w` onto a prefix (`pref_it`). So `w` is the concatenation of level-`J` blocks `σ^{2J}(w_i)` starting at `pos J i`, and every position lies in exactly one block (`exists_block`).
4. If every block is at least `n` long, a factor of length `n` starting in block `i` ends by the end of block `i+1`. It is `(σ^{2J}(w_i w_{i+1})).drop o |>.take n` with `o < ℓ_J(w_i)` (`factor_in_blocks`).
5. Let `j` be least with `n ≤ S_j` and `J = j + 1`. Then blocks are at least `n` long by 2, and `S_j ≤ 3(k²+2) n` by minimality, so each block is at most `3(k²+2)² n` long. Counting triples `(a, b, o)` gives `9 · 3(k²+2)² n`.

Greedy digits: interior digits give every remainder in `[0,1)` (`Base.value_lt_one`), and `β · R_{n-1} = d_n + R_n` then forces `d_n = ⌊β R_{n-1}⌋`.

Pisot facts: from `m r + r² = 1` alone; `X² - mX - 1 = (X - β)(X + r)`.

Bounded complexity: prefixes map length-`n+1` factors onto length-`n` factors, so counts are nondecreasing. Bounded counts are then equal at some `n ≥ 1`, where the prefix map is injective (`Set.ncard_image_iff`). So each window determines the next, and pigeonhole on windows gives eventual periodicity.

## External implication (not formalized)

[Adamczewski–Bugeaud, Corollary 1](https://doi.org/10.1017/S0143385707000223): for `β` Pisot or Salem and algebraic `ξ ∈ [0,1]`, the greedy `β`-expansion has bounded complexity or `liminf p(n)/n = ∞`. `xi_complexity_unbounded` excludes the bounded alternative and `xi_inputs` the superlinear one. Hence `ξ_{k,m}` is transcendental for `k ≥ 1`, `m ≥ 4`. Only the corollary is external. Neither it nor transcendence is a Lean declaration, and no axiom or hypothesis stands for them.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

Both modules are in the root import closure. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Negative controls

- At `k = 0` the entries `(1,0)` and `(2,1)` of `M²` are `0`, so step 2 fails as stated and `entry_bounds` carries `1 ≤ k`.
- A factor longer than the next block can span three blocks. `factor_in_blocks` carries `n ≤ ℓ_J(b)` for every `b` and is applied only at `J = j + 1`.
- `greedy` needs every digit below `m`. At `m = 3` the digit `3` would allow a remainder at or above `1`.

## Non-claims / remaining gaps

- Transcendence of `ξ_{k,m}` rests on the external corollary, which is not formalized. Every hypothesis it places on `β` and on the expansion, and both of its alternatives' negations, are compiled.
- Whether `ξ_{k,m}` or the family is new is not addressed.
- The constant `27 (k²+2)²` is not optimized.
- Irreducibility of `X² - mX - 1` is not proved. The Pisot conclusion does not need it: a rational root would be an integer `> 1`.
- The golden-ratio block coding `0 ↦ 0000, 1 ↦ 0010, 2 ↦ 0100` is not treated.
