# Receipts: proof of the zero-fibre anchor theorem

The mathematics, its scope and its non-claims are in
[the proof note](../../docs/c4-zero-fibre-anchor-proof-2026-11-22.md).
For `k ≥ 2`, Lean proves that any two tilings over the zero solenoid
history share a labelled tile. Zero fibre only; no ledger claim changes.

- Lean `4.34.0-rc2`, Mathlib `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`,
  options `-DautoImplicit=false -Dpp.unicode.fun=true`. Dependency
  `.olean` files already in the container were reused; the project
  modules were built from source in this session.
- Mojo `1.1.0.dev2026090805`.

| File | Content |
| --- | --- |
| `OriginCycleAxioms.lean` | `#check` of eleven declarations and `#print axioms` of fourteen |
| `origin-cycle-axioms.log` | its output: fourteen closures, each `propext, Classical.choice, Quot.sound` |
| `test-origin-cycle.log` | the contract receipt of `kernel/tests/test_origin_cycle.mojo` |

Local receipts. Hosted CI has not run on this revision, and independent
human review is pending.

Replay:

```sh
cd proof/PscVerif
lake build PscVerif.C4ParameterFamilyOriginCycle
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  ../../evidence/c4-zero-fibre-anchor-proof-2026-11-22/OriginCycleAxioms.lean
cd ../../kernel
mojo run -I . -I tests tests/test_origin_cycle.mojo
```
