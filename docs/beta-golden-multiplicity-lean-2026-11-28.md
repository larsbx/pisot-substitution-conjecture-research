# Golden-base multiplicity (countable versus continuum) in Lean (2026-11-28)

Status: compiled Lean specialization of a known theorem. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Source decision: [beta-numeration research route](beta-numeration-research-route-2026-11-27.md), "Formalizing the multiplicity statement requires more than finding one collision or a finite-prefix count". Prior art: Sidorov–Vershik, as recalled by [Ge and Tan](https://arxiv.org/abs/1504.01704); no novelty is claimed. The interval is extended from `(0,1)` to `(0,φ)`.

## Assumptions and hypotheses

Module [`PscVerif.BetaGoldenMultiplicity`](../proof/PscVerif/PscVerif/BetaGoldenMultiplicity.lean), over the golden endpoint and coding modules. `expansions x = {d : ℕ → Bool | value d = x}`, all `{0,1}` streams, not a selected language. `InZ x` is `∃ a b : ℤ, x = a + bφ`. Internally `φ` is the opaque `ph := φ`, because Mathlib's `φ` is an abbreviation and `ring` would otherwise unfold it to `(1+√5)/2`.

## Statement

| Declaration | Content |
| --- | --- |
| `expansions_countable` | `InZ x →` countably many expansions |
| `expansions_infinite` | `InZ x, 0 < x < φ →` infinitely many expansions |
| `expansions_not_countable` | `0 ≤ x ≤ φ, ¬ InZ x →` uncountably many expansions |
| `golden_classification` | the two cases for `0 < x < φ`, stated with Mathlib's `φ` |

With `isUnique_iff` of the endpoint module (`0` and `φ` each have one expansion), every `x ∈ [0, φ]` is classified.

## Derivation / reduction

Remainders `y_n = value(d_n d_{n+1} …)` satisfy `y_{n+1} = φ y_n - d_n` and `0 ≤ y_n ≤ φ` (`st_succ`, `st_mem`).

Countable case:

1. For `x = a₀ + b₀φ`, `y_n = a_n + b_n φ` with `(a_{n+1}, b_{n+1}) = (b_n - d_n, a_n + b_n)` (`st_eq_ev`). The conjugate `z_n = a_n + b_n(1-φ)` satisfies `z_{n+1} = (1-φ) z_n - d_n` (`cj_succ`), so `|z_{m+k}| ≤ φ^{-k} |z_m| + φ² (1 - φ^{-k})` (`cj_iter`).
2. So `|z_n| ≤ |z_0| + φ²`. With `y_n ∈ [0,φ]` this bounds `a_n, b_n`, and pigeonhole gives `n < n'` with equal pairs (`exists_isT`).
3. At a repeated pair, step 1 with `k = n' - n` gives `|z_n| ≤ φ²`. The only points of `ℤ[φ] ∩ [0,φ]` with conjugate in `[-φ², φ²]` are `0, φ⁻¹, 1, φ, 2-φ` (`five`, by integer case analysis). `2 - φ` is followed by `φ⁻¹`, and the set `T = {0, φ⁻¹, 1, φ}` is closed (`isT_succ`), so `2 - φ` never repeats (`isT_of_cycle`).
4. On `T`, `0` and `φ` are absorbing and otherwise the remainders alternate `φ⁻¹, 1`. So the digits are eventually `2`-periodic (`eventually_two_periodic`), and such streams form a countable set (`countable_eventually_two_periodic`).

Infinite case: `0` is entered only from `{0, φ⁻¹}` and `φ` only from `{1, φ}`, so the first visit of an expansion to `T` is at `φ⁻¹` or `1`. Splicing `(01)^j 1 0^∞` (value `φ⁻¹`), or `1` followed by it (value `1`), after that prefix gives an injective family indexed by `j` (`altR_injective`, `splice_injective`).

Uncountable case:

1. `run x b` picks digit `0` below `φ⁻¹`, digit `1` above `1`, and the next unused bit of `b` on `[φ⁻¹, 1]`. It stays in `[0, φ]`, and `x = psum_n + φ^{-n} y_n` gives `value (runD x b) = x` (`run_value`).
2. `ℤ[φ]` is closed under the inverse step `y = φ⁻¹ (y' + d)`, so for `x ∉ ℤ[φ]` no remainder lies in `ℤ[φ]` (`run_not_inZ`); in particular none is `0, φ⁻¹, 1, φ`.
3. Below `φ⁻¹` the remainder is multiplied by `φ`; above `1` its distance to `φ` is. Both grow without bound, so the run enters `(φ⁻¹, 1)` after every time (`run_branches`) and uses every bit (`count_unbounded`).
4. Runs for bit streams agreeing below `K` agree until the `K`-th choice (`run_agree`). At that choice the remainder is strictly inside `(φ⁻¹, 1)`, so different bits give different digits (`runD_injective`). An injection from `ℕ → Bool` refutes countability.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The module is in the root import closure. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`. The finite state enumeration of step 3 has an independent Quint replay; see the [Quint note](beta-numeration-quint-2026-11-28.md).

## Negative controls

- `2 - φ` passes the conjugate bound of step 3 with equality, so a proof that stopped at the bound would wrongly admit a fifth cycle state. `isT_of_cycle` excludes it explicitly.
- At `x = φ⁻¹ ∈ ℤ[φ]` the run with all bits `0` reaches `T` at time `0`; the infinite case handles `n₁ = 0` separately.
- `expansions_infinite` needs `0 < x < φ`: `x = 0` and `x = φ` are in `ℤ[φ]` and have exactly one expansion.

## Non-claims / remaining gaps

- The cardinality of the uncountable case is not identified with `2^ℵ₀` as a Lean statement, although an injection from `ℕ → Bool` into a subset of `ℕ → Bool` gives it.
- No statement for other bases or alphabets.
