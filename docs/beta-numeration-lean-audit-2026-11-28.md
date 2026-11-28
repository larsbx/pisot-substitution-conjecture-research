# Typed endpoint audit for the beta-numeration Lean modules (2026-11-28)

Status: acceptance tooling for already compiled results. No new mathematics, no PSC claim, ledger entry, vendor pin or theorem status change.

This closes the recurring non-claim "no dedicated typed-endpoint audit file accompanies the module" in the beta notes.

## What the audit checks

Replay script [`proof/PscVerif/BetaNumerationAudit.lean`](../proof/PscVerif/BetaNumerationAudit.lean), run in an isolated workspace by [`tools/check_beta_numeration_lean.sh`](../tools/check_beta_numeration_lean.sh) and by the [`beta-numeration-lean.yml`](../.github/workflows/beta-numeration-lean.yml) workflow.

1. **Every local constant** of the eleven modules `BetaGoldenEndpoint`, `BetaMetallicUnique`, `BetaMetallicNormalForm`, `BetaFamilyFixedWord`, `BetaFamilyComplexity`, `BetaFamilyXi`, `BetaFactorBounded`, `BetaGoldenCoding`, `BetaGoldenMultiplicity`, `BetaMetallicCarry` and `BetaMetallicSchmidt` is checked for local axioms and for axioms outside `propext`, `Classical.choice` and `Quot.sound`. That is 696 declarations, 584 of them theorems.
2. **Seventeen endpoints** must be theorems owned by their stated module, with a type definitionally equal to an independently written acceptance type. The types are the uniqueness classifications (golden, metallic, normal form, cardinalities), non-periodicity and linear complexity of `w`, bounded-complexity periodicity, greedy golden coding, golden multiplicity, the seven-state criterion and its reachability, and Schmidt periodicity with `ξ_{k,m} ∉ ℚ(β_m)`, irrationality and `golden_code_not_mem`.
3. **Forty refusal controls.** For every endpoint, a wrong-typed theorem and a missing declaration must be refused. In addition, six altered contracts must be refused:
   - the golden classification with only `0^∞`;
   - metallic uncountability from `m ≥ 2`;
   - non-periodicity without `k ≥ 1`;
   - Schmidt without the greedy hypothesis;
   - the seven-state criterion with "some time" in place of "every time";
   - golden multiplicity with countable and uncountable swapped.

## Replay

```sh
./tools/setup_lean.sh
./tools/check_beta_numeration_lean.sh
```

The runner copies sources only (`make_proof_bank.py --prepare-audit-workspace`) and never local `.olean` caches. It verifies the Lean and Lake pins before and after the build, and requires exactly `PSC_BETA_MODULE ×11`, `PSC_BETA_ENDPOINT ×17`, `PSC_BETA_CONTRACT_REFUSED ×6`, `PSC_BETA_REFUSAL_CONTROLS 40` and `PSC_BETA_AUDIT_COMPLETE 17 696 584`.

## Negative controls

The six altered contracts above. They are the overstrong or weakened variants each note names as its negative control, now enforced mechanically rather than only stated.

## Non-claims / remaining gaps

- The counts bind the current sources. Adding a declaration to a beta module changes them, and the runner fails closed until they are updated deliberately.
- The audit does not replace the complete `tools/check_lean.sh` gate, which compiles the whole root import closure.
