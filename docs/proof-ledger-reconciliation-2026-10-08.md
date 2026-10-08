# Proof-ledger reconciliation — 2026-10-08

**Scope:** reconcile PRs [#236](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/236),
[#237](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/237), and
[#241](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/241).
The live baseline is `main@33a1b8b6cffc10c7f1e5be41a22325897a5072e4`:
#241 was already merged before this reconciliation. Its nine canonical names,
four G1 alternatives and formal-productivity assumption model are retained.
The remaining contributions are integrated in #237; #236 is superseded only
after the integration is validated and merged.

Inspected source heads: #236 `608f4b4978a8297c345587c622bd5e7afdaae762`,
#237 `9e99184156e52e80a32c7457222572367af80a93`, and #241
`ebc815f1b1bf2ba32b11a94462f9b575762954d7`. This reconciliation changes no
open mathematical premise to proved and changes no finite-domain claim scope.

## One representation of each result

| Source definitions | Canonical representation | Reason |
| --- | --- | --- |
| #236 `PotentialOverlapFiniteDescent` and `OverlapCycleBoxBound`; #237 `PotentialOverlapFiniteDescent`; #241 `BoxCycleContainment` | `BoxCycleContainment` | Both parts of Ω1 remain grouped in the merged node; the finite descendant graph is per starting overlap, not the entire potential-overlap set. |
| #236 `BoxFormalProductivityEquivalence`; #237 `BoxProductivityEquivalence`; #241 `BoxAutomatonCertificate` | `BoxAutomatonCertificate` | Theorem Ω is the per-specimen equivalence between formal productivity and a complete productive box. |
| #236 `PisotMeyerProperty`; #237 `PisotFamilyMeyerProperty`; Meyer hypothesis folded into #241's import | `PisotMeyerProperty` | A separate literature import makes the scalar Pisot, repetitivity and FLC hypothesis transfer visible. |
| All three overlap-coincidence imports | `OverlapCoincidenceCriterion` | One imported sufficiency criterion for occurring overlaps with Meyer return vectors; no new converse is registered. |
| #236 `BoxAutomatonPDSCertificate`; #237 `BoxPDSCertificate` | `BoxAutomatonPDSCertificate` | A per-specimen implication with its executable premise inside the statement. This is distinct from assuming productivity uniformly. |
| #241 `FormalProductivity` and consequences (a)–(c) | `FormalProductivity`, `PDSFormalProductivityRoute`, `PDSFormalProductivitySeedRoute`, `G1FormalProductivityRoute` | The universal premise stays open. Consequence (a) derives from the per-specimen certificate; the other two routes retain their existing mechanism and dependencies. |
| #236 sign/periodic-pair nodes; #237 sign/periodic-pair nodes; #241 `LeftmostChainCycleStructure` | `LeftmostChainCycleStructure` | Lemma S, LC and LC4 remain grouped. The zero index is on the later-starting side; the prefix object is a right-infinite ray. |
| #236 and #241 `LeftmostChainG1Certificate` | `LeftmostChainG1Certificate` | LC5 remains a per-specimen implication, never a sufficient branch establishing uniform G1. |

No competing names in this table are registered as additional theorem nodes.
`tools/make_ledger.py` owns the definitions and generated relationships.
Content-addressed record IDs change when evidence or dependency content changes;
all edges and G1 alternatives are regenerated against the resulting IDs.
Canonical names are retained rather than copying incompatible old digests.

The direct certificate's dependency closure is exactly:
`BoxAutomatonPDSCertificate`, `BoxAutomatonCertificate`, `BoxCycleContainment`,
`PisotMeyerProperty`, and `OverlapCoincidenceCriterion`. It contains no
Theorem B, Lemma C, Proposition F, Theorem R, Theorem S or Proposition V(2).
Neither import alone establishes it. The uniform overlap-coincidence route
additionally needs the open `FormalProductivity` gate.

`MCLedgerFormalProductivityGateAssumed` retains the FP scenario and now assumes
the explicit Meyer import as well as overlap coincidence and the density bridge.
It reaches G1 and both PDS route nodes while leaving canonical PDS, SCC Producer
and the seed gates unestablished. Open/import-only scenarios leave uniform G1,
PDS and formal productivity unestablished. These models check dependency
establishment; they do not prove a mathematical theorem or a specimen verdict.

## Review and computational evidence retained

The independent [#236 review](review-box-leftmost-ledger-2026-10-08.md) and
[#237 audit](proof-bank-audit-2026-10-08.md) remain available alongside #241's
append-only side-notes review. The Ω1, Ω, direct certificate, literature and LC
records bind the review sources, date, inspected baseline, reconciliation
locator and pending human review. The previously reviewed source counts and
proposed names are mapped here; they are not competing live ledgers.

The scope corrections retain the nonsingular field-embedding justification,
actual-overlap hypothesis transfer, invertibility of `I-M^r`, later-starting
index convention, half-line comparison, periodic starting-letter count, and
opposite-sign argument for mirror cycles. The leftmost fixed-centre proof
retains #241's removal of the unnecessary Lemma C dependency.

The standing LC census has 10,584 sign/shape checks, 10,128 integral replays
and 456 uncomputed offsets. These warrants stay separate. The #236 completion
gate raises on a capped graph, inconsistent sign/shape totals or failed
integral replay. Uncomputed long offsets remain labelled uncomputed. This is
a repair of exit-status semantics, not a new full census or universal claim.

## Lean infrastructure and the two P2 repairs

#237's shared provisioning/build scripts, pinned direct Lake requirement,
compiled-declaration audit, session hook, CI integration and generated proof
bank are retained. Its spectral evidence correction cites the archived
certificate; the centralizer and trace lemmas remain partial Lean support.
The box/LC theorems and literature imports have no complete Lean binding.

1. `lean_declarations` now scans `PscVerif.lean` alongside nested library
   modules. The adjacent replay script is not a library module. A regression
   inserts a root theorem and lemma and requires both in the inventory and
   compiled-audit receipt.
2. Lake checkout verification compares HEAD and rejects tracked index or
   working-tree changes, including deletions and untracked files; an unreadable Git status also
   refuses verification. Real temporary Git checkouts test both pin-check
   modes with staged, unstaged, deleted and untracked sources at an unchanged
   pinned HEAD. Ignored build caches are allowed.

The original seven P2 regression cases failed against the #237 checker.
Current-head review then found the untracked-source gap in the first repair;
two additional negative cases reproduce it before the final refusal check.
All nine cases pass with these repairs. Existing audit controls still reject missing
receipts, incomplete cached output, nonstandard axioms and failed builds.
The proof bank is an inventory of governed claims, named source proofs and
apparent statement openings. Actual Lean evidence requires the fresh compiled
audit; source inventory completeness conveys no mathematical proof authority.

## Validation

Current validation and any unavailable toolchain are recorded in #237's
updated evidence table before merge. Generated ledger, TLA+, governance,
relationship and proof-bank artifacts are regenerated from their sources.
The run does not claim human peer review, a proof of PSC, a uniform G1/PDS
verdict, or completed tensor/spectral formalization.
