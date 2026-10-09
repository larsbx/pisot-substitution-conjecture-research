# Theorem Ω audit receipts — 2026-10-08

Source snapshot: PR #233 final head
`72f173dbc8dc0de1e5e13503b2911e0411d1fda8`, merged as
`cb9db58c9e25209c2a54ccd6955b509af88e8356`. The CI checkout
`1c5128de9e4fab2c93f2493c99235f27bd663987` and source head have the same Git
tree, `86c6b2a5274fca5105a26f1c2e961c8a1864440a`; this was checked through
the Git data API, rather than assuming a PR run checked out its head.

`representatives.jsonl` is the unmodified independent Python oracle output
for the named canonical Mojo graph exports. Every edge, overlap, projected
start set, shortest depth and recurrent coordinate was checked with exact
integer/rational arithmetic. The positive controls include determinants 3
and 2 and a two-real-conjugate specimen. `domain-cardinalities.json` is an
independent exact matrix/Parikh-weighted count of the domains and their union.
These are computational audit receipts, not independent mathematical review.

Replay from the repository root, with its supported Mojo compiler:

```sh
mojo run -I kernel kernel/omega_box_audit.mojo > /tmp/omega-boxes.txt
PYTHONPATH=reference python oracles/python/omega_box_audit.py /tmp/omega-boxes.txt
PYTHONPATH=reference python oracles/python/omega_domain_audit.py
mojo run -I kernel kernel/tests/test_vertex_coincidence.mojo
```

The exporter is a wrapper around the existing canonical kernels. Its full
7.1 MiB export is reproducible and is identified by SHA-256 in every oracle
receipt; it is not duplicated here. The independent oracle uses rational
interval refinement rather than the canonical Sturm–Tarski sign kernel.
The input kernel closure has no changes relative to the source snapshot.

`vertex-regression.log` preserves the local seven-test regression output.
`negative-calibrations.log` records rejection of a deleted child, an altered
depth, an incorrect field, and a missing start represented by a duplicate
state, in an in-memory copy of the Tribonacci export.
`mojo-suite.log` preserves the complete successful 68-file canonical suite.

`ci-snapshot.json` records observed statuses, including unfinished jobs.
`census-excerpts.log` contains verbatim timestamped census-output excerpts
from GitHub job logs, with their original order retained within each job.
The source jobs and runs are identified by the JSON snapshot. Seven completed
length-4 slices cover 79,325 specimens; the other five are not credited.
Neither this snapshot nor this packet represents the entire larger census
as completed. Later results require a separately dated record.

`ci-followup.json` is a later snapshot: slices 00, 05, 06 and 10 have also
passed, bringing completed length-4 coverage to 124,657 specimens. Their
timestamped output is in `census-followup-excerpts.log`. Slice 09 remains
unfinished in that snapshot. The initial records above are unchanged.

`ci-completion.json` is the final snapshot: all thirteen box jobs and all
twenty research-check jobs succeeded on the source head. Actual output counts
sum to 135,990 formally productive length-4 specimens, with zero caps,
nonproductive specimens or failures. The total-length-8 job certifies 24,486.
`census-completion-excerpts.log` preserves the final slice-09 output, and
`box-depth-followup.log` supplies depth lines for the four intervening slices.
The exact 14,670-member intersection gives a 145,806-member certified union.
Earlier incomplete snapshots are retained unchanged.

`verification-final.log` records local verification: Python, TLA+, provenance,
generation and governance passed; the runner skipped Mojo because Pixi is
absent, and Lake failed to detect its installed configuration. The complete
Mojo suite was run separately and passed. The source-head CI Lean job passed;
none of these Lean checks formalize Ω. No independent human mathematical
acceptance is represented by this packet.

The proof audit and remaining acceptance conditions are in
[`docs/audit-theorem-omega-2026-10-08.md`](../../docs/audit-theorem-omega-2026-10-08.md).
