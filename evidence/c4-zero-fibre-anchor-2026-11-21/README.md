# Receipts: zero-fibre anchor reduction

The mathematics, its scope and its non-claims are in
[the note](../../docs/c4-zero-fibre-anchor-stop-go-2026-11-21.md). The
anchor theorem is reduced to an arithmetic premise; the premise is **not**
proved.

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
| `origin-cycle-census.log` | `kernel/c4_family_origin_cycles.mojo`, `k = 1..12`, box 8, step cap 4096 |
| `SHA256SUMS` | digests of the three files above and of the sources they were produced from |

These are local receipts. Hosted CI has not run on this revision.

Replay:

```sh
cd proof/PscVerif
lake build PscVerif.C4ParameterFamilyZeroFibreAnchor
lake env lean -DautoImplicit=false -Dpp.unicode.fun=true \
  ../../evidence/c4-zero-fibre-anchor-2026-11-21/AnchorAxioms.lean
cd ../../kernel
mojo run -I . -I tests tests/test_origin_cycle.mojo
mojo run -I . c4_family_origin_cycles.mojo
```
