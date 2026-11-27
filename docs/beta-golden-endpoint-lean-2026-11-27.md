# Golden-base endpoint theorem in Lean (2026-11-27)

Status: compiled Lean specialization of a known result. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Source decision: [beta-numeration research route](beta-numeration-research-route-2026-11-27.md), first deliverable. Prior art: Glendinning and Sidorov (2001), cited there; no novelty is claimed.

## Statement

Module [`PscVerif.BetaGoldenEndpoint`](../proof/PscVerif/PscVerif/BetaGoldenEndpoint.lean). Streams are `d : ℕ → Bool`, indexed from zero; `r = φ⁻¹`; `value d = ∑' n, digit (d n) * r ^ (n + 1)`; `IsUnique d` means every stream `e` with `value e = value d` equals `d`. The quantifier ranges over all `{0,1}` streams, not over a greedy or otherwise selected language.

| Declaration | Content |
| --- | --- |
| `isUnique_iff` | `IsUnique d ↔ d = 0^∞ ∨ d = 1^∞` |
| `value_zero`, `value_one` | the two values are `0` and `φ` |
| `value_nonneg`, `value_le` | every value lies in `[0, φ]` |
| `value_of_isUnique` | a uniquely represented value is `0` or `φ` |
| `eq_zero_of_isUnique_of_lt_one` | below `1` the only unique stream is `0^∞` |

## Derivation

1. `r_sq_add`: `r² + r = 1`, from `φ² = φ + 1` and `φ r = 1`.
2. `value_cons`: `value (b t) = digit b · r + r · value t`, from summability by comparison with the geometric series.
3. `value_100_eq_011`: the prefixes `100` and `011` have equal value before any common tail; the difference is `-r (r² + r - 1)`.
4. `value_alternating`: a stream starting at `0` and changing digit at every step satisfies `V = r (r + r V)`, hence `V = r`, the value of `1000…` (`value_one_zeros`).
5. `IsUnique.tail`, `IsUnique.shift`: uniqueness passes to every tail, by prepending the removed digits to a competing tail.
6. `IsUnique.change_at`: by 3 and 5, `d m ≠ d (m+1)` forces `d (m+1) ≠ d (m+2)`.
7. `IsUnique.constant`: a nonconstant unique stream has a first change at `n`, alternates from `n` by 6, and its tail from `n` or `n+1` starts at `0`; 4 and 5 give a second representation. Contradiction.
8. `isUnique_zero`, `isUnique_one`: a nonnegative series with sum zero vanishes termwise, applied to `value e` and to `value 1^∞ - value e`.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The module is in the root import closure, so the complete declaration audit covers it. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Negative controls

Both collisions named in the route note are theorems of the module, not prose: `value_100_eq_011` (100/011) and `value_01_periodic_eq_one_zeros` (`(01)^∞` against `1000…`). Either refutes the overstrong variant "a stream with no two adjacent ones is unique".

## Non-claims and remaining gaps

- No greedy-admissibility statement, no multiplicity statement (countable against continuum), nothing about the metallic family `β² = mβ + 1` with `m ≥ 2`.
- No Mojo implementation or oracle corresponds to this module; the upstream quadratic carry semantics belongs to `larsbx/finite-math-kernels` and is not vendored here.
- No dedicated typed-endpoint audit file accompanies the module; drift of the statement is guarded only by the generic declaration audit.
- No substitution word, complexity bound or transcendence statement is touched.
