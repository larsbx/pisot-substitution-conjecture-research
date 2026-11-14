# Follow-up scope and verification history

This documentation follow-up records the proportional family stop/go review
and preserves the unsuccessful local Lean attempts made while the hosted
acceptance of PR #569 at `84f7b2b70adbd632c0e0cc06cbd246aee2020f70` was
running. That candidate subsequently failed; its original hosted evidence is
preserved below. The current successor is
`8a6bd5732fefba94ad4fef5df2333065c1302452`, tree
`a7dcb3ebf30f3bb686d8f1beb3545dec26df8448`. No compiled theorem is accepted
by the historical records in this packet.

## Hosted explicit-only failure

The original full-isolated Lean run
[43568767809](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43568767809),
job `132368324108`, and original-archive run
[43568767783](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43568767783),
job `132368324164`, both completed with failure at exact source
`84f7b2b70adbd632c0e0cc06cbd246aee2020f70`, tree
`2add5458cf28d2d0c63256644c1ee766dc978897`, attempt 1. Both generated carrier
modules compiled. The consumer exceeded the default recursion limit at
`NamedForwardCarrier.lean:76:83`, in the fixture-1 local `rfl` equality,
before its explicit checker transport. Neither run reached complete compiled
axiom acceptance or the original nine-endpoint archive replay.

`hosted-failure-84f7b2b7.tar.gz` preserves the 13 original files and their
original inner manifest: raw terminal run/jobs responses, complete job logs,
raw artifact metadata, the actual failed artifact ZIP, its verified transport
receipt, the failure summary and the prepared diagnostic sources. The ZIP's
1,183,331 bytes match provider artifact `14104507713` and SHA-256
`481dcc840e8cb68c3240eaa01b2ae0c34899b0b81f52b6a466a14c8671c2b3fa`.
Its seven members are pre-failure records; they contain no original-payload
nine-endpoint receipts. The success-only extraction helper was prepared but
not used to certify this failed run. No artifact code or acceptance inspector
was executed against the failed artifact.

The generic selector-lemma signature probe compiled only the abstract
compositions with pinned Mathlib, using `propext`. It did not compile the
production carrier application. The successor uses those generic selector
proofs and scopes `maxRecDepth 200000` to the one consumer theorem; acceptance
of that successor requires its own exact-source production evidence.

## Local outcomes

| Attempt | Terminal outcome | Elapsed seconds | Scope |
| --- | --- | ---: | --- |
| Actual unchanged generated fixture-0 checker | SIGKILL (`-9`), no object, empty log; cause unconfirmed | 929.842 | Source SHA-256 `5026901eb6a7f9c2500f38f7835aa96a235c6eb0e5722da1084a45fb83b2b905`, cached dependencies, one Lean worker |
| Original selector body with both real state tables | Owned 180-second cap, SIGTERM (`-15`), no object | 180.140 | Fixture-0 check is an explicit theorem hypothesis |
| Repaired selector body with both real state tables | Owned 180-second cap, SIGTERM (`-15`), no object | 180.305 | Same conditional diagnostic |
| Repaired-only diagnostic with progress commands | Interpreter memory exception under explicit `-M1024`, SIGABRT (`-6`), no object | 541.311 | Time cap did not fire; progress commands may add interpreter overhead |

Every recorded input remained unchanged. No local recursion-depth diagnostic
or completed axiom report was produced. These results are resource-limited
and inconclusive; they are neither production acceptance nor mathematical
counterexamples. The production checker run supplied no confirmed reason for
its signal. The diagnostic memory exception does not identify which command
was processing, and no import-stall claim is made.

The conditional diagnostic imports the actual cached fixture-1 checker and
retains both original literal state tables. It copies fixture-0's exact
substitution, packet and state-list definitions, but leaves its successful
check as an explicit theorem hypothesis. It cannot certify the full two-fixture
consumer. A read-only existence scan found all 14 project modules and all
3,486 modules in this diagnostic's complete source-import closure; existence
is not object/source correspondence or isolated dependency trust.

## Retention and replay boundary

`local-diagnostics.tar.gz` preserves the original scripts, sources, logs,
receipts, source hashes and cache-existence records. It also retains the
earlier 18-file diagnostic manifest. Extract into a new empty directory and
run `sha256sum --check SHA256SUMS` there. The scripts retain their original
local paths and cached-dependency assumptions; replaying them is not a
replacement for `tools/check_lean.sh` or the original-archive gate.

The family review is in
[the stop/go note](../../docs/c4-parameter-family-stop-go-2026-11-14.md).
Its symbolic derivations were hand-checked and independently reviewed by
another agent; they have no compiled acceptance receipt. The decision redirects
an unnecessary root-nullity search toward the remaining finite forward-carrier
obligation. All governed claims retain their previous status.

The parent candidate remains unchanged while its hosted acceptance runs. This
follow-up changes documentation and historical evidence only. Any successful
hosted result must remain bound to the source revision that produced it.

`SHA256SUMS` pins every other file in this packet.
