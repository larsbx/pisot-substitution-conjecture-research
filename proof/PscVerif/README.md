# PscVerif — Lean 4 proofs for PSC research

Lean checks the exact algebraic statements in these modules. A partial binding
does not prove its full parent claim; the tensor, intertwining, semisimplicity
and Galois arguments are not completely formalized. Universal PSC and uniform
G1/PDS remain unresolved. See [the proof bank](../../docs/proof-bank.md),
[verification architecture](../../docs/verification-architecture.md), and
[the spectral module](PscVerif/Spectral.lean) for scope and evidence.

From the repository root:

```bash
./tools/setup_lean.sh
./tools/check_lean.sh
```

Both scripts force the checked-in compiler release and reject executable
version mismatches. Setup prepares the development environment; formal audit
credit requires the isolated checker. It excludes caller compiled caches,
verifies clean pinned dependency sources, obtains Mathlib artifacts from the
fixed upstream source-hash cache, compiles PSC and replays the complete local
declaration audit. The compiler and upstream cache remain explicit trust inputs.
Every inventoried proof must be reached. Only `propext`, `Classical.choice` and
`Quot.sound` are accepted; `sorryAx`, local axioms, missing proofs or a missing
completion receipt refuse verification. Inventory and individual `#print axioms`
lines alone do not satisfy this gate.

`PscVerif.SelectedRank` additionally proves finite selected-path rank descent,
semantic path transfer, and descendant productivity under explicit seed-cover
and all-edge closure hypotheses. Its finite counterexample proves why local
selected ranks alone do not supply closure. Mojo-to-Lean implementation
refinement and uniform X-descendant productivity remain separate obligations;
see the [selected-rank interface](../../docs/selected-rank-soundness-2026-10-31.md).

`PscVerif.OverlapContraction` provides the deductive layer for PR #496's
overlap-certificate argument: fixed-iterate uniqueness and period-three
compatibility, a kernel-decidable integer occurrence-graph checker and its
real soundness theorem, complete-cover measure subadditivity, null-overlap
inference, and exclusion of a positive-measure carrier covered by null roots.
Parallel occurrences remain separate. `PscVerif.OverlapPacket` adds a checked
external-data format, typed-certificate binding and kernel rejection controls.
The [concrete replay gate](../../docs/c4-overlap-lean-packet-binding-2026-11-05.md)
requires all generated proofs, declaration audits and full emitted-packet parity
before crediting class acceptance. Geometric coverage, the M-adic construction
and the strict-cut counting lower bound remain separate obligations. See the
[overlap Lean interface](../../docs/c4-overlap-lean-interface-2026-11-05.md)
for the exact hypotheses and remaining bindings. No C4 or PSC status changes.
