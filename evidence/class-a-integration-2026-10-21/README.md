# Class-A CI scope and concurrent-main reconciliation

PR #303 has 63 successful checks at 2f30628; its merge 902c68e has the
identical b748716 tree. `pr303.json` and `pr303-checks.json` retain the raw
API snapshot data; deterministic gzip copies are also provided. The two
*-jobs.json files retain step summaries from the run-jobs connector. The two
numbered .log files are unedited raw dedicated-job logs. Source comparison
against that completed scope shows every old kernel/reference source and
both class-A workflows/oracles unchanged, except the two additive Pixi tasks.

`pre-repair-refusal.log` preserves the actual refusal on that manifest
extension. `focused-tests.log` and `accepted-class-d-audit.json` record the
local successful compatibility repair and unchanged class-D historical scope.
See `docs/class-a-integration-2026-10-21.md` for exact semantics and controls.
No fresh combined-head CI success or main merge is inferred from this packet.
The historical review and open-universal labels remain unchanged.

`SHA256SUMS` covers every file here except itself.
