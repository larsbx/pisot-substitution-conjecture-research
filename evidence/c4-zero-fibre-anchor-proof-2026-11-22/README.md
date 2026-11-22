# Receipts: proof of the zero-fibre anchor theorem

The mathematics, its scope and its non-claims are in
[the proof note](../../docs/c4-zero-fibre-anchor-proof-2026-11-22.md).
For `k ≥ 2`, Lean proves the classification of periodic interior lattice
tiles and gives a common labelled tile for any pair over the zero solenoid
history. The census and regression cover the explicit finite domains below.

- Lean `4.34.0-rc2`, Mathlib `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`,
  options `-DautoImplicit=false -Dpp.unicode.fun=true`. The audited
  proof and fixture are from `f9553feb687598aa63848ef749687ba21b4e4266`.
- Mojo `1.1.0.dev2026090805` (`34562fa1`), resolved via `kernel/pixi.lock`.

| File | Content |
| --- | --- |
| `OriginCycleAxioms.lean` | `#check` of eleven declarations and `#print axioms` of fourteen |
| `origin-cycle-axioms.log` | its output: fourteen closures, each `propext, Classical.choice, Quot.sound` |
| `test-origin-cycle.log` | Exact regressions, including first cycle entry at step 18 for `(1;8,2,-8)` and refusal at cap 17 |
| `origin-cycle-census.log` | Regenerated box-8 census for `k = 1..12` with step cap 4096 |

The corrected maxima are `44, 18, 11, 8, 7, 6, 5, 6, 5, 5, 5, 5`.
The reached cycles and tile counts agree with the original census.
[Historical log](../c4-zero-fibre-anchor-2026-11-21/origin-cycle-census.log)

These are local receipts. Hosted acceptance and independent human review
are pending.

Replay:

```sh
cd proof/PscVerif
lake build PscVerif.C4ParameterFamilyOriginCycle
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  ../../evidence/c4-zero-fibre-anchor-proof-2026-11-22/OriginCycleAxioms.lean
cd ../../kernel
pixi run --locked mojo run -I . -I tests tests/test_origin_cycle.mojo
pixi run --locked mojo run -I . c4_family_origin_cycles.mojo
```
