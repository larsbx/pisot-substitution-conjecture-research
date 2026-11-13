# Separate data modules and concrete checker replay

This packet records the canonical data-module split, complete native
reproduction and successful compilation of both actual Init-only data
modules. **The data-module results alone do not establish either complete
carrier, the named termination consumers, or isolated axiom acceptance.**

## Exact separation

`NamedForwardCarrierWords0.lean` and `NamedForwardCarrierWords1.lean`
import only `Init`. They contain the unchanged typed chunks, ordered
states, state accessors, checked index aliases, child rows and ordered
seed function. The corresponding `NamedForwardCarrierDataN.lean` imports
its own Words module and `FastForwardCarrier`, retaining the exact
substitution, packet and every proof obligation.

Independent block comparison against the preceding archived monolithic
exports verified that the data declarations, substitution declaration,
and complete packet/proof suffix remain byte-identical. Only import and
module placement changed in this split. The earlier checked-index and
singleton changes are documented in the
[intermediate packet](../shared-index-row-checks/README.md).

The canonical Mojo exporter emits the payload with `--lean-data` and the
checker with `--lean`. Default JSON output is unchanged. The native gate
now hashes, emits and compares all four files, records their names, and
the workflow triggers on both source families. The archived Lean replay
also includes both new Words files in its candidate-source and isolated
workspace comparisons. The root import closure and compiled audit include
their owned declarations through the checker modules.

| Actual source | SHA-256 |
| --- | --- |
| Words 0 | `6583596c0d3d21a11a3e283954ec4c8ad72572969155e406bb2cd6f6baceb72a` |
| Words 1 | `a44fee6794080f4f0cde90167c862476b6022115a7e3120078dff042c153702b` |
| Checker 0 | `5026901eb6a7f9c2500f38f7835aa96a235c6eb0e5722da1084a45fb83b2b905` |
| Checker 1 | `a49d8fa4146b534cff95259beab31a06903088184676704c239eb11b98cc4c0a` |

## Complete native replay

`native-replay.tar.gz` retains the entire updated gate output. It passed
in **110.235957 seconds**, with **258 tests passing in 101.12 seconds**.
Both original JSON packets and all four generated Lean files reproduced
byte for byte. Native controls, both empty-output budget refusals and the
optimized independent oracle passed. Source bytes, revision and supplied
executable hashes remained unchanged.

The 28 new controls retain all 230 prior checks and verify the actual
import binding before resolving a payload. They reject wrong or missing
fixture modules, extra or duplicated imports, missing dependencies,
swapped fixture bodies and wrong namespaces. The wrong-module control
supplies readable, valid payload bytes under the wrong module name.
Correct unused data therefore cannot substitute for the imported payload.

The local run records parent HEAD
`55ce68531aecb7a351e652dd5cf824ee8ac32a34` with the candidate edits present.
Its source manifest identifies the tested bytes. This is a source-bound
local result, not a hosted or clean-parent acceptance claim. The separate
source-bound rebuild reproduced exactly the supplied exporter binary;
the gate does not claim to have rebuilt its supplied executables.

| Native identity | SHA-256 |
| --- | --- |
| Exporter binary | `7a4fbd3567ccc2c0750d366985cf895d8aa9f115d20a3492035e033220c5faca` |
| Replay receipt | `59e0b0f00c163470e15913de0c5d10942bdf87af0c94b762c2253fe94558523d` |
| Source manifest | `4f07c9c2c83b119301af80abc2bb5a647c9a8baa30a067963f89ac79a706cad8` |
| Native checksum manifest | `6ce1b11ae77b6318a869c92b7a100fe6d4c3b46afd6d4541f7ace589d2563963` |

`governance-checks.tar.gz` retains the subsequent validation receipt and
logs: 12 archived-endpoint protocol tests, 57 proof-bank tests and 166
recorded-evidence integrity tests passed. Together with the 258 native
carrier tests, these are **493 passing focused tests**. Generated source
inventory, vendored pins, ledger generation, Markdown integrity, claim
governance and whitespace checks also passed. The inventory contains 126
claims and 3,597 named Lean proofs; its increase comes from separating the
existing row decisions, and no governed status is promoted.

## Actual compiled data modules

`compiled-init-payloads.tar.gz` retains both exact generated sources,
compiled objects, start/terminal receipts, full logs and sampled resource
histories. These were serial actual-module compilations using the pinned
Lean compiler, separate from the earlier prefix probe.

| Actual module | Result | Elapsed seconds | Peak sampled RSS bytes |
| --- | --- | ---: | ---: |
| `NamedForwardCarrierWords0` | Exit 0, object produced, source unchanged | 35.010425 | 741,531,648 |
| `NamedForwardCarrierWords1` | Exit 0, object produced, source unchanged | 35.024152 | 744,415,232 |

The object hashes are
`26922864e4a01f5b0004387deea57c3a9bdc51ba7a4cddb70656d4e461f23fa7`
and
`a812f56bf162e515d1641b6f01cbfb412d1b428fcaffe898dd4ba5b2cc08c67a`,
respectively. These successful compilations check the closed data
definitions and explicit bounds; they exclude the carrier's row-validity,
closure and termination proofs.

## Remaining formal acceptance

Both checker modules still require complete terminal compilation, followed
by their named consumers and both original archive imports with all nine
exact semantic endpoints. The isolated full build and compiled
allowed-axiom audit remain required. A focused run binds the relevant
payload source/object and generic checker object in its start receipt;
cached-dependency development checks do not replace the isolated gate.

All historical unsuccessful runs retain their original outcomes. No
`native_decide`, new axiom, placeholder, weaker carrier predicate, or
general PSC claim is introduced. All 126 governed claim statuses remain
unchanged.
