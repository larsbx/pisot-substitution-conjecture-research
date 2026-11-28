# Quint finite models for the beta-numeration route (2026-11-28)

Status: finite-domain evidence for stated boxes and parameters, replayed with exact integer arithmetic. It corroborates, and does not replace, the universal Lean theorems. No PSC claim, ledger entry, vendor pin or theorem status changes.

Model [`proof/quint/BetaNumeration.qnt`](../proof/quint/BetaNumeration.qnt); runner [`tools/check_beta_numeration_quint.py`](../tools/check_beta_numeration_quint.py); CI [`beta-numeration-quint.yml`](../.github/workflows/beta-numeration-quint.yml).

## Assumptions and hypotheses

Elements `u + v√D` are compared through the integer sign function `sgn`, so no floating point enters. Golden points are pairs `(a, b)` for `a + bφ` with `a, b ∈ [-4, 4]`. Metallic carries are pairs `(a, b)` for `a + bβ_m`, with `m ∈ {1, …, 6}` and box `[-(2m+6), 2m+6]²`. The model imports nothing from Lean.

## What is checked

| Module | Test | Finite statement | Lean counterpart |
| --- | --- | --- | --- |
| `GoldenOrbit` | `candidateStatesTest` | the box points in `[0, φ]` with conjugate in `[-φ², φ²]` are exactly `0, 1, φ⁻¹, φ, 2-φ` | `BetaGoldenMultiplicity.five` |
| | `cycleStatesTest` | the box points on a cycle of the remainder graph are exactly `0, φ⁻¹, 1, φ` | `isT_of_cycle` |
| | `closedSetTest`, `exactTransitionsTest` | `{0, φ⁻¹, 1, φ}` is closed, with transitions `0→0`, `φ⁻¹→{1,0}`, `1→{φ,φ⁻¹}`, `φ→φ` | `next_of_*`, `isT_succ` |
| | `entryTest` | `0` is entered only from `{0, φ⁻¹}`, `φ` only from `{1, φ}` | the first-visit step of `expansions_infinite` |
| | `twoMinusPhiTest` | `2 - φ` moves only to `φ⁻¹` and lies on no cycle | `isT_of_cycle`, last case |
| `MetallicCarry` | `everyBoundedStateContinuesTest` | every box state with `|z| ≤ 1 + r` has a successor in the set | the real-interval continuation behind `value_eq_iff_bounded` |
| | `sevenReachableStatesTest` | for each `m ≤ 6`, exactly 7 states are reachable from `(0,0)`: `0, ±1, ±r, ±(1+r)`, that is `(0,0), (±1,0), (-m,1), (1-m,1), (m,-1), (m-1,-1)` | `value_eq_iff_states` (finiteness only) |
| | `collision100Test`, `metallicCollisionTest` | `100/011` (`m = 1`) and `a 0 c / (a-1) m (c+1)` (`m ≥ 2`) return the carry to `(0,0)` | `carry_100_011`, `value_carry` |
| `BetaAdversarial` | `conjugateBoundIsSharpTest` | `2 - φ` meets the conjugate bound with equality | negative control of the multiplicity note |
| | `unboundedCarryRejectedTest` | `1 0^∞` against `0^∞` leaves the state set | negative control of the carry note |
| | `forcedDigitTest`, `nonVacuousStatesTest` | the digit at `2 - φ` is forced to `0`; each state set has more than 7 elements | — |

## Evidence and replay

```sh
python3 tools/check_beta_numeration_quint.py --output "$OUT"
```

The runner pins Quint `0.33.1`, the `typescript` backend and seed `20261128`. It checks the declared test inventory against the source, runs every test, and requires each of five mutants to fail its named assertion with `QNT508`. It binds the model and runner digests and the Git revision in `quint-receipt.json`, and refuses a stale or changed source. Local run on this branch: 16 tests passed, 5 mutants rejected.

## Negative controls

The five mutants: dropping the lower conjugate bound, flipping the digit sign in the remainder step, ignoring the return in the cycle test, transposing the carry transition, and tightening the carry bound to `|z| ≤ r`.

A side finding from the mutation run: loosening the upper carry bound from `1 + r` to `2 + r` does not change the live or reachable states. States above `1 + r` diverge under `z ↦ βz - m`, whose fixed point is `1 + r`, and are pruned as non-live. The mutant that loosened the bound therefore survived and was replaced by the tightening mutant.

## Non-claims / remaining gaps

- The seven-state count is checked only for `m ≤ 6`. No Lean theorem identifies the reachable set for general `m`.
- The golden checks are confined to the coordinate box; their universal versions are the Lean theorems in the table.
