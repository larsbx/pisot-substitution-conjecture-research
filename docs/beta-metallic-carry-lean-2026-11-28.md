# Finite-state carry criterion for equal metallic values in Lean (2026-11-28)

Status: compiled Lean specialization of known theory. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Source decision: [beta-numeration research route](beta-numeration-research-route-2026-11-27.md), the carry-equality paragraph. Prior art: Pisot finite-state normalization, [Frougny](https://fpsac-archive.github.io/FPSAC93/ARTICLES/Frougny.pdf); no novelty is claimed. The upstream contract in `larsbx/finite-math-kernels` is outside this session's repository scope and was not read. The seven-state criterion below was derived independently, and the [Quint replay](beta-numeration-quint-2026-11-28.md) recomputes it for `m ≤ 6`.

## Assumptions and hypotheses

Module [`PscVerif.BetaMetallicCarry`](../proof/PscVerif/PscVerif/BetaMetallicCarry.lean). `B : Base m` (`m r + r² = 1`, `β = r⁻¹`). For streams `d, e` over `{0, …, m}`, `δ_n = d_n - e_n ∈ [-m, m]` and

`carryPair 0 = (0,0)`, `carryPair (n+1) = (b_n + δ_n, a_n + m b_n)`,

with value `zval (a,b) = a + bβ` and conjugate `zconj (a,b) = a - b r`.

## Statement

| Declaration | Content |
| --- | --- |
| `zval_succ`, `zconj_succ` | `z_{n+1} = β z_n + δ_n`, `z'_{n+1} = -r z'_n + δ_n` |
| `psum_diff` | `Σ_{j<n} δ_j r^{j+1} = r^n z_n` |
| `value_eq_iff_bounded` | `value d = value e ↔ ∀ n, |z_n| ≤ 1 + r`, and `↔ ∃ C, ∀ n, |z_n| ≤ C` |
| `conj_bound` | always `|z'_n| ≤ m/(1 - r)` |
| `value_eq_iff_states` | `value d = value e ↔ ∀ n, carryPair n ∈ states B` |
| `states_finite` | `states B` (box pairs with `|a + bβ| ≤ 1 + r`) is finite |
| `value_eq_iff_seven` | for every `m ≥ 1`: `value d = value e ↔` every carry lies in `seven m = {(0,0), (±1,0), (-m,1), (1-m,1), (m,-1), (m-1,-1)}`, the values `0, ±1, ±r, ±(1+r)` |
| `seven_reachable` | for every `m ≥ 1`, each of the seven carries occurs for some pair of streams with equal values |
| `carry_100_011` | at `m = 1`, `100t` against `011t` returns the carry to `(0,0)` after three digits |

## Derivation / reduction

1. The transitions follow from `β² = mβ + 1` and `m r + r² = 1`.
2. `psum_diff` by induction, using `βr = 1`.
3. Equal values: subtracting `value = psum_n + r^n · tail_n` for `d` and `e` gives `z_n = tail_n(e) - tail_n(d) ∈ [-(1+r), 1+r]`, by `value_nonneg` and `value_le_top`.
4. Bounded carry: `|psum_n(d) - psum_n(e)| ≤ C r^n → 0`, while the partial sums converge to the values, so the values agree.
5. `|z'_{n+1}| ≤ r |z'_n| + m` and `m/(1-r)` is the fixed point, so `conj_bound` holds by induction from `z'_0 = 0`.
6. `b(β + r) = z - z'` and `a = z' + b r` turn both bounds into `|a|, |b| ≤ side B = ⌈1 + r + 2m/(1-r)⌉`.
7. Seven states (`seven_step`). From a state in `seven m` the next second coordinate `a + m b` is `0` or `±1`, and the first is `b + δ` with `|δ| ≤ m`. With `β = m + r`, the bound `|z| ≤ 1 + r` cancels `r` and leaves integer conditions: `|a'| ≤ 1` when `b' = 0`, `a' ≤ 1 - m` when `b' = 1`, `a' ≥ m - 1` when `b' = -1`. The digit bound supplies the other side, so the next state is again in `seven m`. Induction from `(0,0)` and the bounded criterion give `value_eq_iff_seven`.
8. Reachability (`seven_reachable`). Four difference walks, `(1, -m, -1, 0, …)`, `(1, 1-m, -m, -m, …)` and their negatives, stay in `seven m` and visit all seven states. `±(1+r)` is absorbing under `δ = ∓m`. A bounded difference sequence is realized by `d = δ⁺`, `e = δ⁻` (`delta_real`), so the converse of step 7 makes the two streams equal in value.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The module is in the root import closure. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound` (`carry_100_011` uses only `propext`).

## Negative controls

- `1 0^∞` against `0^∞` has `δ = (1, 0, 0, …)`. At `m = 1` the carry runs `(1,0), (0,1), (1,1), (1,2), …` with Fibonacci growth, so it is unbounded and the values differ. The Quint replay checks that it leaves the state set.
- `value_eq_iff_states` needs both the box and the real bound. The box alone admits pairs with `|a + bβ| > 1 + r`.

## Non-claims / remaining gaps

- No Mojo implementation; Mojo is not available in this environment, and the canonical kernel belongs upstream.
- None on the automaton itself: containment and reachability of the seven states are both compiled for every `m ≥ 1`. Quint replays them independently for `m ≤ 6`.
