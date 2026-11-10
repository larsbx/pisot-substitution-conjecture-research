# Overlap verification integration against main

## Assumptions and hypotheses

The user authorized opening the work against main and merging it on November 6.
PR #501 now incorporates verification PR #500 and main
`873316d517934e9f669a93c4a81d9db5ff84e7b8`. It retains the canonical packet
scope and all four geometric/measure bindings in the
[packet audit](c4-overlap-canonical-packet-audit-2026-11-06.md).

## Derivation / reduction

Both merges conflicted in the append-only side-note history. Main integration
also conflicted in the generated proof-bank Markdown. Both histories were
retained, and proof-bank JSON/Markdown were regenerated from the merged inputs:
126 claims, 106 named Lean proofs and 383 source openings. The three parent
side-note histories remain subsequences of the integrated history.

The full Lean project, canonical exporter, imported native overlap engines,
vendored dependency sources and pinned configurations are byte-identical to
PR #500 head `19882f9f7ac85ede2b6eca3eab0d74cb4406439d`. The follow-up's
runtime oracle, mutation tests, artifact auditor and bad-binding fixture are
byte-identical to accepted PR #501 head
`c5d4c56df3fec9e34bde31eebb23a8f73d48c488`. The per-file hashes are retained
with the integration evidence. No mathematical implementation is changed by
this reconciliation. Main's separately scoped two-tail Lean work is retained.

Six inherited evidence directories lacked `SHA256SUMS`. Their tracked bytes
were compared with their committed copies before adding complete manifests;
the manifests attest file identity and completeness, not mathematical validity.
Main already contains the correction to the stale `C4StandingCorpus`
claim-coverage expectation. Earlier failed CI observations remain historical.

## Evidence and replay

The exact parent PR #500 has successful
[all-18 kernel packet acceptance](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42220994601)
and [generic Lean acceptance](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42220994675).
The exact original PR #501 also has successful
[all-18 acceptance](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42184035576),
including its stronger mutation tests and runtime oracle comparison.

Fresh local integration validation: **231 focused tests passed**, all 32
generated ledger surfaces are current, proof-bank consistency passes, the
historical class-C source audit passes, and all claim-governance checks pass.
The focused set covers the packet/protocol mutations, proof-bank guards,
claim coverage, every recorded-data checksum, historical source manifests,
Markdown source provenance and links.

```sh
uv run --offline --no-project --with pytest --with sympy python -m pytest \
  tests/test_overlap_lean_packet_replay.py tests/test_proof_bank.py \
  tests/test_claim_coverage.py tests/test_claim_governance.py \
  tests/test_recorded_data_integrity.py tests/test_research_source_manifest.py \
  tests/test_check_markdown_source.py tests/test_markdown_links.py -q
python tools/make_proof_bank.py --check
python tools/make_ledger.py --check
python tools/check_class_c_below_three_integration.py
PYTHONPATH=tools python -m claim_governance.cli --root .
```

Receipts and source hashes are in
`evidence/c4-overlap-main-merge-2026-11-06/`. These distinguish unchanged-source
acceptance at the parent revisions from fresh local integration checks.
They do not assert a newly completed integrated-head kernel run. The dedicated
hosted gates remain enabled for the integrated PR head. The branch has no
required GitHub status checks; this merge uses the completed source-equivalent
parent kernel evidence and passing local integration checks.

## Negative controls

Existing invalid targets, hidden payload, wrong layout, zero weights,
missing rows, repeated-occurrence counting, equal-weight wrong-target and
omitted/duplicated/collapsed occurrence controls remain unchanged. The
independent expected-type auditor still refuses misleading `True` proofs.
All checksum, provenance and claim-coverage guards remain enabled.

## Non-claims / remaining gaps

No general PSC/C4/PDS status is promoted. Geometric graph/cover refinement,
matrix-adic Haar/product scaling, actual compact-prefix contraction and
fixed-origin strict-cut counting remain explicit obligations. User merge
approval does not constitute independent mathematical review. Earlier
exact-revision receipts retain their original identities and scopes.
