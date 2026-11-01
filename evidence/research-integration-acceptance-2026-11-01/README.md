# Completed broad local replay supplement

2026-11-01; parent public revision 8de671ce8540a006091f3205aadf7d448c52d818.
Its tree is identical to local 4c2278d2f490a46f7672ee893487a8c8d0960bd0.
The broad Python run started on the d8090a04 source tree; the subsequent
commit changes documentation and appends ledger entries only. The native,
Python, workflow and governed source bytes were unchanged during this run.
The targeted source/integrity/link checks were repeated after the doc changes.

All 174 test files were partitioned in sorted order into four disjoint
round-robin shards, each run with:

    python3 -m pytest -o addopts= -q <shard file list>

The exact file lists, timings and exit codes are in python-summary.json.
The totals are 1,293 passed and 3 skipped; no skips count as acceptance.
All 18 original TLA+ models have their expected outcome using the unchanged
proof/tla/check.sh (including the expected NonProductive counterexample).
The jar is the release downloaded by the same URL as the committed CI workflow.
Source-integrity/link checks: 130 passed; claim governance: all six checks pass.

This supplement does not rewrite the earlier packet, promote any claim,
waive a pending hosted check, or credit the incomplete local Lean audit.
The original packet preserves that failed Lean startup and initial row-12
compiler failure alongside the corrected native replay.
