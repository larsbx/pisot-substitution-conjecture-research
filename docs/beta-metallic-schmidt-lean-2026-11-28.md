# Schmidt periodicity in metallic bases and ξ_{k,m} ∉ ℚ(β_m) in Lean (2026-11-28)

Status: compiled Lean specialization of K. Schmidt (1980) to quadratic metallic bases, with corollaries for the literal family. Transcendence stays external. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Source decision: [novelty and transcendence stop/go](beta-xi-novelty-stop-go-2026-11-28.md), "Proceed".

## Assumptions and hypotheses

Module [`PscVerif.BetaMetallicSchmidt`](../proof/PscVerif/PscVerif/BetaMetallicSchmidt.lean). `B : Base m`, `β = B.beta = r⁻¹`. The remainders of `d` are `rem d n = value (shift d n)`. "Greedy" means every remainder is below `1`; `digit_eq_floor` shows this makes every digit `⌊β · remainder⌋`, the β-transformation digit. Membership in `ℚ(β)` is stated concretely as `∃ a b q : ℤ, 0 < q ∧ q x = a + bβ`, which describes all of `ℚ(β)` because `β` is quadratic.

## Statement

| Declaration | Content |
| --- | --- |
| `Base.eventuallyPeriodic_of_mem` | greedy `d` and `q · value d = a + bβ` with `q > 0` imply `d` is eventually periodic |
| `xi_not_mem` | `k ≥ 1`, `m ≥ 4`: `ξ_{k,m} ∉ ℚ(β_m)` |
| `xi_irrational` | `k ≥ 1`, `m ≥ 4`: `ξ_{k,m}` is irrational |
| `golden_code_not_mem` | `k ≥ 1`: the value of the golden block coding is not in `ℚ(φ)` |

## Derivation / reduction

1. `q R_n = a_n + b_n β` with integer coordinates `(a, b) ↦ (b - q d_n, a + m b)`, from `β² = mβ + 1` (`rem_coords`).
2. The conjugate `a_n - b_n r` satisfies `z' ↦ -r z' - q d_n`, so `|z'_n| ≤ |z'_0| + qm/(1-r)` (`conj_coords_bound`).
3. With `q R_n ∈ [0, q)` and `β + r ≥ 1`, both coordinates lie in an explicit integer box, and pigeonhole gives a repeated pair, hence a repeated remainder.
4. Greedy digits are functions of remainders, so equal remainders propagate with equal digits (`prop`), and `d` is eventually periodic.
5. `ξ_{k,m}`: its digit stream `w + 1` is greedy (`BetaFamilyXi.greedy`) and not eventually periodic (`shifted_not_eventuallyPeriodic`). The golden coding: its `{0,1}` stream becomes a `Fin 2` stream for the metallic base with `m = 1, β = φ` (`goldenBase`, `goldenBase_value`), and `code_greedy`, `code_not_eventuallyPeriodic` apply.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The module is in the root import closure. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Negative controls

- The greedy hypothesis is essential. At `m = 1` every expansion of an element of `ℤ[φ]` is eventually periodic (`BetaGoldenMultiplicity.expansions_countable`). But `1/2 ∈ ℚ(φ) \ ℤ[φ]` has uncountably many expansions (`expansions_not_countable`), and eventually periodic streams form a countable set, so most of them are not eventually periodic. Greediness of the selected expansion is what forces periodicity.
- For bases that are neither Pisot nor Salem the conclusion fails (Schmidt, as recalled by Adamczewski–Bugeaud). Here the Pisot property enters through `|-r| < 1` in step 2.

## Non-claims / remaining gaps

- Transcendence of `ξ_{k,m}` and of the golden coding's value remains the external Adamczewski–Bugeaud step. Route B (Kebis–Luca–Ouaknine–Scoones–Worrell echoing) still needs its balanced-pair transfer.
- Only the quadratic metallic case of Schmidt's theorem is formalized; not general Pisot or Salem bases.
