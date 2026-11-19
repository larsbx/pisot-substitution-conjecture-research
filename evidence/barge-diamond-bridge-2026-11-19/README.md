# Barge–Diamond bridge evidence

Assessed base: `ec026774e666fb8e8ac43b1ba975b9a4df8891b2`.
The `initial-state.json` snapshot records #608's open/conflicted state and
the 24 new named proofs. No governed claim or source statement changes.

`historical-slice-audit.log` and `historical-slice-bindings.json` preserve the
earlier standalone, source-bound replay against #608 at
`6b175ce350b8691563d8ea254e33bd84445860ef`. It checked all 24 proposed named
proofs, with 212 owned declarations and 147 theorems under standard axioms.
It is not an actual-import or isolated acceptance receipt for this port.

The actual-module check is `lake build PscVerif.BargeDiamondBridgeControls`
followed by `lake env lean BargeDiamondBridgeAudit.lean` in `proof/PscVerif`.
Its local terminal receipt will be recorded separately. Cached upstream and
unchanged project artifacts, if used locally, remain explicit trust inputs.

The `Barge-Diamond word correspondence` workflow builds the actual new modules
in a fresh source-only workspace with pinned upstream checkouts. It rejects
nonstandard axiom closure and missing named-proof coverage. A queued hosted
run is not successful acceptance. The complete whole-library isolated gate is
broader and is not asserted by the scoped workflow.

No existence axiom, BBK identification, rank-two exclusion, universal C4 or
PSC theorem is introduced by these receipts.

## Local attempt boundary

The actual-module attempt was stopped without reaching the two new modules.
It completed 23 dependency modules (20 source-matched cached inputs and
3 fresh compilations). Concurrent compilation remained in unmodified
`CountBridge` and `M0Pisot`; a sequential retry remained in `CountBridge`.
No rejection of the new Lean source was observed, but there is no successful
actual-import receipt or scoped actual-import axiom audit.
`local-import-attempt.json` binds this boundary to the source hashes and
preserves the historical slice result as a separate scope. The isolated
hosted job was queued at inspection. The PR remains a draft and is not
merged on the strength of the historical slice.
