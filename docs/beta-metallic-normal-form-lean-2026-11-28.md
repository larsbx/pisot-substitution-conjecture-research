# Metallic unique expansions: normal form, the interval [0,1) and cardinalities in Lean (2026-11-28)

Status: compiled Lean specialization of known theory. No PSC claim, ledger entry, vendor pin or theorem status changes. Independent human review pending.

Closes the three non-claims of the [metallic unique-expansion note](beta-metallic-unique-lean-2026-11-27.md): the explicit list, the `[0,1)` restriction, and the cardinalities. Source decision: [beta-numeration research route](beta-numeration-research-route-2026-11-27.md).

## Assumptions and hypotheses

Module [`PscVerif.BetaMetallicNormalForm`](../proof/PscVerif/PscVerif/BetaMetallicNormalForm.lean), over `PscVerif.BetaMetallicUnique`. A digit is an endpoint (`IsEnd`) if it is `0` or `m`, interior (`IsInterior`) if it lies in `{1, …, m-1}`. `NormalForm d` means `d = 0^∞`, or `d = m^∞`, or `d = a^r w` with `a` an endpoint, `r ≥ 0` and every digit of `w` interior.

## Statement

| Declaration | Content |
| --- | --- |
| `endpointsInitial_iff` | `m ≥ 1 → (EndpointsInitial d ↔ NormalForm d)`; with `Base.isUnique_iff`, the unique streams are exactly the normal forms |
| `Base.value_lt_one_iff` | for a unique `d`: `value d < 1 ↔` no digit is `m`; so on `[0,1)` the unique streams are `0^∞` and `0^r w` |
| `unique_one` | `m = 1`: the unique set is `{0^∞, 1^∞}` |
| `unique_two_countable`, `unique_two_infinite` | `m = 2`: the unique set is countably infinite |
| `unique_not_countable` | `m ≥ 3`: the unique set is uncountable |

## Derivation / reduction

1. `EndpointsInitial.eq_of_end`: in an endpoint-initial stream an endpoint digit equals every earlier digit, by stepping back with the two defining implications.
2. `endpointsInitial_iff`, forward direction: if some digit is interior, let `r` be the first such index; earlier digits are endpoints, hence all equal `d 0` by step 1; later digits are interior by `interior_from`. If no digit is interior, all digits equal `d 0` and the stream is constant. The reverse direction checks the two implications on each form.
3. `value_lt_one_iff`: a digit `m` forces `d 0 = m` by step 1 and every digit positive by `pos_from`, so `value d = m r + r · value(tail) > m r + r² = 1`. With no digit `m`, `value_lt_one` gives the bound.
4. Cardinalities. At `m = 1` there is no interior digit, so only the constants remain. At `m = 2` the interior alphabet is `{1}`, so the unique set lies in `{0^∞, 2^∞} ∪ {a^r 1^∞}`, which is countable, and `r ↦ 0^r 1^∞` is injective into it. At `m ≥ 3` the map `b ↦ (b_n ? 2 : 1)` injects `ℕ → Bool` into the unique set, and `ℕ → Bool` is not countable by Cantor.

## Evidence and replay

```sh
./tools/setup_lean.sh
./tools/check_lean.sh
```

The module is in the root import closure. Accepted axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Negative controls

- At `m = 3` the stream `1 3 3 …` is not in normal form (an `m` after an interior digit), and `isUnique_iff` gives a second expansion.
- `value_lt_one_iff` needs uniqueness: over `{0,1,2}` the non-unique stream `2 0 0 …` has value `2r = 0.83… < 1` and uses the digit `m`.

## Non-claims / remaining gaps

- No multiplicity statement for non-unique values is made here; for `m = 1` see the golden multiplicity note.
