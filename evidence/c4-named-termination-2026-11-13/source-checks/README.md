# Consumer selector repair: source-validation records

This unpublished packet preserves the source and governance checks for the
selector-only repair in NamedForwardCarrier.check_checkedStates. The checks
ran against a working tree based on commit
1ce54efeff586ecda2ec1bd11a2f9c6617b2fb87. The repaired consumer source is bound
by SHA-256 c825c41da424572c4014ecf2e1f6a80457f9265409c4fde6daf7f3cccd5137e7.
The candidate patch and complete recorded source hashes are retained.

## Results

All seven actual validation commands exited 0:

| Check | Observed result |
| --- | --- |
| Proof-bank tests | 57 passing test symbols, completed at 100%, exit 0; 85.192 seconds |
| Proof-bank consistency | 126 claims, 3,597 named Lean proofs, 411 source openings |
| Vendored package pins | All checked packages match their recorded pins |
| Generated ledger | All 32 generated surfaces are current |
| Claim governance | Terminology, claims, coverage, promotion, numerics, consistency all pass |
| Working-tree whitespace | Exit 0, empty diagnostic log |
| Staged whitespace | Exit 0, empty diagnostic log |

The exact argument vectors, Python interpreter, environment overrides, UTC
start/terminal times, return codes and log hashes are recorded in the original
per-command JSON records. Commands were:

    python -B -m pytest --assert=plain -q -p no:cacheprovider tests/test_proof_bank.py
    python -B tools/make_proof_bank.py --check
    python -B tools/vendoring/check_vendored_sync.py
    python -B tools/make_ledger.py --check
    PYTHONPATH=tools python -B -m claim_governance.cli --root .
    git diff --check
    git diff --cached --check

All 1,960 recorded source, documentation and configuration files stayed
unchanged during the checks and the subsequent strict log review. Packaging
also checked their recorded hashes against the available repository bytes.
SOURCES.sha256 is an input-hash inventory; it does not embed those source files.

## Preserved wrapper failure and separate result review

The initial wrapper marked its aggregate status as failed because its parser
expected a numeric "57 passed" summary line. The repository config sets
addopts="-q", and the command also supplies -q. This double-quiet output omitted
that summary while retaining exactly 57 pass dots followed by [100%]. Pytest
itself exited 0.

The initial failed aggregate receipt, runner and logs are preserved byte for
byte. They were not rewritten to show success. A separate executed
review_completed_checks.py verified the exact 57-dot completion line, process
exit 0, the six other successful command records, all recorded source hashes,
and the original receipt/log digests. Its review.json records the passing
source-validation result and the original wrapper parser failure explicitly.
No test was rerun for this review or packaging step.

## Archive layout and integrity

The archive root contains this README, a complete SHA256SUMS for every other
regular-file member, and the packaging verification code and receipt.
The records/ directory contains all 30 original files, including the original
records/SHA256SUMS, records/REVIEW.sha256, records/SOURCES.sha256, initial
failed terminal.json, separate passing review.json, every command log and
start/terminal record, and both executed validation/review scripts.

The separate directory preserves the original manifest bytes and their
relative-name semantics. Both original integrity manifests were verified
against the original records and again against the archived bytes. The source
input manifest was verified against the repository files; its own exact bytes
are covered by the original and outer integrity manifests.

The tar contains only safe, unique regular-file paths, with fixed permissions,
zero timestamps and fixed owner fields. The gzip header has a zero timestamp
and empty filename. Every archived original record was compared byte for byte
with its retained original. The enclosing archive digest is recorded in the
parent evidence inventory and publication report.

## Scope

These are source, test and governance checks. No Lean compiler or native gate
was invoked. This packet does not establish compiled acceptance of the repaired
consumer, the full isolated Lean build, original-packet proof imports, a
nine-endpoint compiled axiom audit, or termination acceptance. Those gates
retain their separate receipts and status.
