# Receipts: zero-fibre anchor reduction

This historical packet records the anchor reduction to C(k). The next
increment proves C(k) and records the corrected census. [Reduction and scope](../../docs/c4-zero-fibre-anchor-stop-go-2026-11-21.md)

- Base revision: `7258dccf1265243c67c62c3979272507c8957c25`.
- Lean `4.34.0-rc2`, Mathlib `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`,
  options `-DautoImplicit=false -Dpp.unicode.fun=true`. The dependency
  `.olean` files already in the container were reused; the project
  modules were built from source in this session.
- Mojo `1.1.0.dev2026090805`.

| File | Content |
| --- | --- |
| `AnchorAxioms.lean` | `#check` and `#print axioms` for the new declarations |
| `anchor-axioms.log` | its output: ten closures, each `propext, Classical.choice, Quot.sound` |
| `origin-cycle-census.log` | Original `k = 1..12`, box-8 census with step cap 4096. Its largest transient is understated for five parameters. |
| `SHA256SUMS` | digests of the files of this packet |

These receipts were recorded locally for the reduction.

Replay the historical logs from `eb95c7fcd698dab65f149b637ac750bccef6502d`.

```sh
cd proof/PscVerif
lake build PscVerif.C4ParameterFamilyZeroFibreAnchor
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  ../../evidence/c4-zero-fibre-anchor-2026-11-21/AnchorAxioms.lean
cd ../../kernel
mojo run -I . -I tests tests/test_origin_cycle.mojo
mojo run -I . c4_family_origin_cycles.mojo
```

## Correction, 2026-11-22

The original census measured only the new prefix when an orbit reached
a cached tile. Its log is retained as a record of that run. The corrected
maximum at `k = 2` is 18. The exact tile counts and reached cycles agree
with this historical run for all twelve parameters.
[Current census and replay](../c4-zero-fibre-anchor-proof-2026-11-22/README.md)
