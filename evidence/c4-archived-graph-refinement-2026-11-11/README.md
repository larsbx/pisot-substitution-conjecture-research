# Archived graph refinement: acceptance boundaries

The mathematical derivation, remaining hypotheses and replay commands are
in [the implementation note](../../docs/c4-archived-graph-refinement-2026-11-11.md).
The pre-code source decision was committed as
`249b31a7` on baseline `99748ca29ee4bc3daf259da1fdabaffa3d5d4793`.

## Independent executable replay

[`native-oracle/`](native-oracle/README.md) contains exact-source local
receipts for both entire original graphs, their full positional and nested
addresses, normalized slots, rooted discovery and complete ordered
forward/inverse comparison. The actual native packet matched the
independent oracle. Historical graph digests and positive potentials are
unchanged. The new address digests are separate and do not overwrite the
archive.

The local replay rejects 24 native and 30 independent oracle mutation
attempts. Nine independent tests pass with the actual native packet.
Receipt source hashes authenticate the specific files exercised; later
published-head CI is separately required. The full native packet is a
reproducible development/CI artifact whose hash and size are recorded in
`native-oracle/local-replay.json`.

## Lean development probes

[`development/`](development/) records pinned local source compilation,
including per-module source/dependency hashes and losslessly compressed
compiler logs. These probes use recursively source-matched development
imports from the same pinned Lean/Mathlib environment. They are **not**
the canonical isolated-source acceptance gate.

All seven new modules passed their final source-matched development probes,
covering 76 named proofs. The generated full inventory contains 2,555 named
Lean proofs and the same 126 governed claims. Each successful module receipt
pins the actual source and its recursive project dependencies; the final
wrapper includes the finite decoded-candidate closure equivalence.

The first monolithic bridge probe was killed by the runtime before any
compilation success was reported. It is not credited as a proof failure
or a proof success. The generic row/refinement layer was subsequently
separated from the named Haar consumer, and compilers were serialized.
The sharp-box first elaboration exposed finite-matrix simplification,
namespace and interval-case proof errors; those were repaired without
changing the mathematical statements. The first digit probe exposed a
missing expected type in a prefix-concatenation inequality; no endpoint
kernel computation was rejected. Failed and successful probes retain
separate logs and outcomes.

## Canonical exact-revision acceptance

The implementation PR records the published commit, tree, workflow URLs,
results and compiled axiom inventory. Acceptance requires a successful
complete `tools/check_lean.sh` run from isolated sources at that exact
published head, reaching every inventoried declaration, plus the exact-head
native/oracle workflow. Successful older-head or cached-local results do
not certify a changed head.

The full compiled audit retains the existing allowance of `propext`,
`Classical.choice` and `Quot.sound`. No new axiom, `sorry` or native decision
axiom is admitted. The generated proof bank and existing source-pin and
governance regressions are separate consistency gates.

## Hosted recorded-data integrity repair

At published head `e1646baa5fdedd2bc937b7e2f7788f8e55d268c2`, the
[`historical-sources` job](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43139692291/job/130923404285)
failed three recorded-data integrity tests. This new packet was missing
its `SHA256SUMS`. Separately, the unchanged #549 named-overlap packet uses
nested paths relative to its own directory, while the common reader treated
those paths as repository-relative. The original manifests and records in
both historical packet exceptions remain byte-for-byte unchanged.

The bounded repair adds this packet's complete manifest with explicit
`./`-prefixed relative paths and adds the named-overlap packet to the
reader's existing explicit packet-relative exception set. Every digest,
file-existence check, exact-file-set check and Git-tracking check remains
enforced. No mathematical or native source changes are involved.

[`historical-hosted/e1646baa-historical-sources.json`](historical-hosted/e1646baa-historical-sources.json)
records the exact failed job, its decoded log digest and the distinction
between the newly missing manifest and the preexisting path interpretation.
Its losslessly compressed log is retained alongside the receipt. That
failed run stopped before its source-pin report, proof-bank check and claim
audit; it supplies no acceptance credit for those steps. Successful checks
at a later revision must be recorded separately.

## What these receipts do not assert

The native/oracle decoder is source-bound and exhaustive within the stated
original rooted construction. Its successful output is not a Lean proof
term for the concrete historical `TableBinding`, `CandidateClosed`,
root/discovery or integer-certificate hypotheses. The new geometric box,
residue and conditional representation/consumer theorems do not hide that
remaining finite payload-import boundary.

No all-`strictPackets` identification, positive strict-root Haar measure,
C4 or general PSC promotion follows from these receipts. Independent human
review remains pending.
