# Metallic unique-expansion theorem in Lean (2026-11-27)

Status: compiled Lean specialization of known theory. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Source decision: [beta-numeration research route](beta-numeration-research-route-2026-11-27.md), section "Uniform quadratic family". It generalizes the [golden-base endpoint theorem](beta-golden-endpoint-lean-2026-11-27.md) from `m = 1` to every `m ≥ 1`. No novelty is claimed.

## Assumptions and hypotheses

Module [`PscVerif.BetaMetallicUnique`](../proof/PscVerif/PscVerif/BetaMetallicUnique.lean). A `Base m` is a real `r` with `0 < r`, `1 ≤ m` and `m r + r² = 1`; `r` stands for `β⁻¹`, `β² = mβ + 1`. Streams are `d : ℕ → Fin (m + 1)`, indexed from zero. `B.value d = ∑' n, d n · r ^ (n + 1)`. `B.IsUnique d` quantifies over every stream on the full alphabet `{0, …, m}`, not over a greedy language.

`EndpointsInitial d` is the conjunction

- `∀ n, d (n+1) = 0 → d n = 0`,
- `∀ n, d (n+1) = m → d n = m`.

Since `0 ≠ m`, these streams are exactly `0^∞`, `m^∞`, `0^r w` and `m^r w` with every digit of `w` in `{1, …, m-1}`. The equivalence with that list is read off here, not a Lean declaration; `EndpointsInitial.interior_from` and `EndpointsInitial.const_of_one` are the compiled parts of it.

## Statement

| Declaration | Content |
| --- | --- |
| `Base.isUnique_iff` | `B.IsUnique d ↔ EndpointsInitial d` |
| `Base.interior` | all digits in `{1, …, m-1}` ⇒ unique, and `r < value d < 1` |
| `Base.IsUnique.const_of_one` | at `m = 1` a unique stream is constant |
| `Base.value_nonneg`, `Base.value_le_top`, `Base.top` | values lie in `[0, 1 + r]`, and `1 + r = m · value 1^∞` is attained by `m^∞` |
| `Base.ofRoot`, `Base.metallic` | a base from any positive root of `β² = mβ + 1`; the explicit `r = (√(m²+4) - m)/2` |

## Derivation / reduction

Write `G = value 1^∞`. Then `G = r + r G`, `m G = 1 + r` (`Base.top`) and `r < G`.

Necessity (`IsUnique.endpointsInitial`):

1. `value_carry`: `a 0 c` and `(a-1) m (c+1)` have equal value before any common tail; the difference is `-r (m r + r² - 1)`.
2. Uniqueness passes to every tail (`IsUnique.of_tail`, `IsUnique.of_shift`).
3. By 1 and 2: `a 0` with `a > 0` is followed by `m` (`head_zero`), and `a m` with `a < m` is followed by `0` (`head_top`).
4. So a positive digit followed by `0` is followed by `(0 m)^∞`, of value `r` (`value_zero_top`); then `a (0 m)^∞` and `(a-1) m^∞` collide, by `m G = 1 + r` (`zero_pred`).
5. Symmetrically a digit below `m` followed by `m` is followed by `(m 0)^∞`, of value `1` (`value_top_zero`); then `a (m 0)^∞` and `(a+1) 0^∞` collide (`top_pred`).

Sufficiency (`isUnique_of_endpointsInitial`):

6. Under `EndpointsInitial`, `d n < m` forces every later digit below `m`, hence the remainder `R_n < 1` (`tail_lt_one`, from `value t + G ≤ m G` and `r < G`); `d n > 0` forces every later digit positive, hence `R_n ≥ G > r` (`lt_tail`).
7. If `e ≠ d` has the same value, take the first differing index `n`. Equal prefixes give `d_n + R_n(d) = e_n + R_n(e)` (`value_shift_eq`). If `d_n < e_n` then `R_n(d) ≥ 1`; if `d_n > e_n` then `R_n(d) ≤ (1 + r) - 1 = r`. Both contradict 6.

This is the remainder criterion of the route note, with the existence of expansions on the full interval replaced by explicit collisions in the necessity direction, so no greedy or lazy algorithm is formalized.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The module is in the root import closure. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Negative controls

Compiled collisions, each refuting uniqueness of a stream outside `EndpointsInitial`: `value_carry` (`a 0 c` against `(a-1) m (c+1)`), `value_zero_top` (`(0 m)^∞` against `1 0^∞`), `value_top_zero` (`(m 0)^∞` against a carry into the previous place). At `m = 1` they are the 100/011 and `(01)^∞`/`1000…` controls of the golden module.

## Non-claims / remaining gaps

- The listed normal form, the statement that only `0^∞` and `0^r w` have value in `[0,1)`, and the countable (`m = 2`) against uncountable (`m ≥ 3`) cardinality are not Lean declarations.
- No greedy admissibility, no multiplicity statement, no finite-state carry automaton; the seven-state equality criterion belongs to `larsbx/finite-math-kernels`.
- No Mojo implementation or oracle corresponds to this module, and no dedicated typed-endpoint audit file accompanies it.
- `Base.interior` gives uniqueness and the interval `(r, 1)` for the candidates `ξ_{k,m}` of the route note once their digits are known to lie in `{1,2,3}` with `m ≥ 4`. It says nothing about the fixed word, its complexity, or transcendence.
