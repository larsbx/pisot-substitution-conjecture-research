# Class-B historical witness replay reconciliation

## Observed failure and provenance

Run [41314198978, job 124870689049](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41314198978/job/124870689049)
failed while comparing `witnesses/plus-g1-q10.labels` after the native
contract, independent graph checks and every original packet checksum passed.
`hosted-failure.log.gz` losslessly preserves the retrieved job log (uncompressed
SHA-256 `8f87062d9f1b42c815e219958c5c3801fb85879b0970947ececf50b380556816`). The job checked out
GitHub PR merge `c6a9256` containing head
`82e84827b83e72865e0e8bd7c271d18101e9baa9` and base `3967ab32`.
The main merge `c27cb596` has the identical mathematical candidate tree.

Commit `669e4630805f43c24b1506f1755dcf8f59baa64d` changed only the graph
builder call in the exporter to the segment-support implementation. The
sorted M/V export is preserved, but W records follow graph discovery order
and select the first descending adjacency child. Discovery and child order
are not mathematical invariants of graph support. The current output's
different bytes must not replace the historical packet or its rank witness.

## Repair and exact contracts

The archived exporter is exactly `kernel/class_b_label_rays.mojo` from
`7c2d83fc8aa44db36662811d914ec146a161d269`, matching the original packet's
source digest `7b42520141e1c68de19f86880ebef1b2b61b3d521f5878798ba2207b2de33747`.
It is compiled with the locked current imports. The unchanged strict replay
wrapper compares all current label files with the current native binary and
all original witness files with the original native exporter. Every byte
comparison remains exact.

Additionally, the independent integer oracle requires the current witness
export to have exactly the archived complete vertex/depth records, then
checks one actual indexed child per non-target, legal letters/ordinals,
direct incidence-plus-prefix shift, and depth decreasing by one. The
historical witnesses pass the same checks. `witness-reconciliation.json`
binds both serializations and their complete coverage counts.

No pinned live mathematical file, existing oracle, source guard, vendored
code, original packet or claim status is modified. The new oracle is a
regression verifier of the existing native witness contract, not a new
graph generator or rank theorem. The old rank-search refusal/counterexample
remains attached to the original witness choices.

## Replay

From `kernel/`, with Mojo 1.1.0.dev2026090805 (34562fa1):

```
pixi run --locked mojo build -I . class_b_label_rays.mojo -o /tmp/current-labels
python ../oracles/python/class_b_label_replay_compat.py --check-source
pixi run --locked mojo build -I . ../archive/class-b-label-witness-export-2026-11-01/class_b_label_rays.mojo -o /tmp/historical-labels
pixi run --locked mojo run -I . tests/test_class_b_label_fit.mojo
```

From repository root:

```
python oracles/python/class_b_label_replay_compat.py /tmp/current-labels /tmp/historical-labels evidence/class-b-label-rays-2026-10-23 /tmp/class-b-replay
python -m pytest -q tests/test_class_b_label_replay_compat.py tests/test_class_b_label_rays.py
python oracles/python/class_b_rank_probe.py evidence/class-b-label-rays-2026-10-23/labels /tmp/rank.json
cmp evidence/class-b-label-rays-2026-10-23/rank-probe.json /tmp/rank.json
```

The focused Python suite has 21 passes, including original-source pin
mutation and malformed/changed/incomplete current-witness refusals. The
existing source/integrity/Class-C/Class-D suite has 150 passes; vendoring,
generated proof-bank/ledger/catalogue and governance checks pass. The
unchanged native contract and original rank-probe result also pass.
`replay.log` and `witness-reconciliation.json` record the completed local
full-label/witness replay; `bindings.json` pins its inputs and outputs.
All 289 current label exports and both historical witness exports matched
byte-for-byte. Each serialization's complete 5,626 witnesses passed the
independent occurrence/shift/descent checks. The original 389-row rank probe
still reports 290 candidates, 99 refusals and its original counterexample;
its JSON is byte-identical to the original packet.

## Acceptance boundary

This supplement preserves a real failed hosted attempt and a later local
repair. It does not turn that failed run green. The repaired Class-B workflow
must pass on the new published head, together with applicable integration,
canonical/Python/formal/provenance/governance checks. Existing mathematical
receipts must retain their exact revision/tree bindings. No independent human
proof certification, general BH/SCC theorem or PSC claim follows.
