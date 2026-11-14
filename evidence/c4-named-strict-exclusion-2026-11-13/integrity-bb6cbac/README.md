# Evidence-packet checksum omission at bb6cbac

[Class-A uniform gap run 43365333191](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43365333191), job `131688284672`, completed with **failure** at commit `bb6cbac16a620da4784f5b30d0a9a242618aef22` (tree `42472cf9f43d2e13bb999fd5c339abfea782d690`). Its pytest invocation reported **1 failed, 217 passed in 52.03s**. The sole reported test failure was `tests/test_recorded_data_integrity.py::test_every_evidence_packet_is_pinned`: this evidence packet lacked its top-level `SHA256SUMS`.

## Work shown

### Assumptions and hypotheses

This record concerns evidence storage integrity. The existing guard requires a top-level checksum manifest in every evidence packet. Its checksum test requires the manifest to name exactly every file held by that packet except the manifest itself; its tracked-file guard requires all listed records and manifests to be present in Git. No mathematical hypothesis or theorem statement changes.

### Derivation / reduction

The failed source omitted `evidence/c4-named-strict-exclusion-2026-11-13/SHA256SUMS`. The evidence worktree still had that same omission before this addition, and source inspection found it was the only evidence packet without a root manifest. The repair adds the missing manifest with full repository-relative paths and SHA256 hashes for every packet file, including this failure record. Earlier evidence files retain their original bytes. Existing tests and checkers are unchanged.

### Evidence and replay

`failure-record.tar.gz` retains exact fresh raw run/jobs JSON, the complete decoded job log, capture timestamps and hashes. It also retains the previously downloaded log separately: that copy has one additional trailing newline, and neither byte sequence was rewritten. `receipt.json` records actual hosted verdicts and the archive manifest. The fresh GET capture completed at `2026-11-13T05:27:03.355Z`. The failed step was `Independent ray oracle and evidence integrity`; subsequent native arithmetic steps were skipped, so the 217 passing tests do not imply that the whole workflow passed.

The focused repair checks are the following existing nodes, run after staging these evidence-only additions so the tracked-file guard observes the intended prospective tree:

```sh
python -B -m pytest -v -p no:cacheprovider tests/test_recorded_data_integrity.py::test_every_evidence_packet_is_pinned
python -B -m pytest -v -p no:cacheprovider 'tests/test_recorded_data_integrity.py::test_checksums_verify[evidence/c4-named-strict-exclusion-2026-11-13/SHA256SUMS]'
python -B -m pytest -v -p no:cacheprovider tests/test_recorded_data_integrity.py::test_pinned_records_are_tracked_for_clean_checkout
sha256sum -c evidence/c4-named-strict-exclusion-2026-11-13/SHA256SUMS
```

Those are replay recipes, not results encoded in this failure record. Actual execution receipts are captured outside the packet after staging, bound to the staged tree. They must not be described as clean-HEAD test results.

### Negative controls

The retained failed hosted run is the observed omission control: the presence guard refused the incomplete packet. The unchanged checksum guard detects altered, omitted or extra packet files; the unchanged tracked-file guard detects records absent from Git. This repair does not bypass those guards or rewrite the historical failure.

### Non-claims / remaining gaps

This record and checksum repair supply no Lean acceptance, native theorem acceptance or new C4/PSC conclusion. Repaired proof acceptance remains a separate gate; earlier pending and failed receipts keep their historical meanings. No successful full workflow verdict is synthesized from the focused integrity repair. No human review is claimed.
