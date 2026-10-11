# PR #235 reconciliation receipts — 2026-10-11

Parents: PR head `7e13a28ec0962a2e09c7666d83ab360962f07b8f` and main
`66df3e4`. The paired audit is
[`docs/audit-theorem-omega-2026-10-11.md`](../../docs/audit-theorem-omega-2026-10-11.md).
This packet does not attest independent human acceptance or universal PSC.

`pr235-head-ci.json` records retrieved workflow/job conclusions for the prior
head, observed October 11. `pr235-head-ci-excerpts.log` holds selected verbatim
timestamped output lines. The logs identify test merge
`6c440aa0b02afd1cb8d1d8b49848a9ee35e30a15`; its tree and the PR head's tree
both equal `e89b686321137090b2c0eeb752edb820cd0b2024`. Do not credit these
as new compiled execution of the reconciled tree. Deduplicate echoed program
and grep-output census lines per job before summing their counts.

Local reconciliation commands, run from the repository root:

```sh
./tools/verify_all.sh
python -m pytest
./proof/tla/check.sh
PYTHONPATH=reference python oracles/python/omega_domain_audit.py
python tools/make_proof_bank.py --check
python tools/check_markdown_source.py
git diff --check
```

`verification.log`: 11 available provenance/governance checks pass; that runner
skips Mojo, pytest, TLA+ and Lean because its PATH/tool discovery was incomplete.
Separate commands provide actual Python and TLA+ execution.
`python-suite.log`: 518 pass, 2 skip, one integrity failure because this new
packet was created during the run and did not yet have its checksum manifest.
After sealing the packet, targeted integrity/governance/proof-bank checks are
rerun separately in `final-targeted.log`. The original failed log is retained.
`tla.log`: all 15 models pass. `domain-cardinalities.json`: independent exact
count again gives 145,806 union / 14,670 intersection. Counting is not a replay
of each overlap graph.

`mojo-provisioning.log`: installation cannot fetch the locked conda-forge
googleapis-common-protos package in this network environment. No Mojo compiler
execution is credited. `lean-provisioning.log`: pinned Lean 4.34.0-rc2 installs
but the executable reports `failed to locate application`; no local Lean proof
execution is credited. An initial tar ownership failure was avoided by using
`TAR_OPTIONS=--no-same-owner`; this did not resolve the runtime limitation.

The reconciled main claim ledger, dependency models and Lean sources are
byte-identical to main. Main's full side-notes ledger remains an exact prefix.
Both previous Ω packets are unchanged against `7e13a28`. Generated proof-bank
counts remain main's 97 claims / 27 named Lean proofs / 269 source openings;
only two existing PDS statement line locators differ. SHA256SUMS pins every
file in this packet. The new-head required CI and independent human
mathematical acceptance remain separate gates.
