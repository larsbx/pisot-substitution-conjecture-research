# PR 659: hosted Lean CI diagnosis

Inspection date: 27 November 2026 (UTC).

Inspected head: `ab71641a847fbce0f1044ecaa968a363eb4c4042`.
Its Git tree is `700c5703f07a41967a2de727debbd33410d10dc7`, matching the reviewed tree.

## C4 overlap Lean verification: hosted runner loss

- Run: [46047918850](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46047918850).
- Job: [140671718261, overlap-proof-bank](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46047918850/job/140671718261).
- Exact job interval: `2026-11-27T18:49:41Z` to `2026-11-27T19:55:44Z` (66 minutes, 3 seconds).
- Workflow: `.github/workflows/c4-overlap-lean.yml`; configured limit: 180 minutes.
- GitHub conclusion: `failure`.

GitHub's [check annotation](https://api.github.com/repos/larsbx/pisot-substitution-conjecture-research/check-runs/140671718261/annotations) states:

> The hosted runner lost communication with the server.

The remaining annotation lists runner termination, CPU or memory starvation, and blocked network access as possible causes. It does not establish which one occurred.

Checkout, exact-revision verification, and pinned-toolchain provisioning succeeded. The compilation/audit step started at `18:51:14Z`; its final metadata remains `in_progress` with no conclusion. Artifact upload and cleanup remain pending. The job log download returned HTTP 404 with Azure `BlobNotFound`, so no compiler-error diagnosis can be recovered from that log endpoint.

This is a reported runner-communication failure, below the workflow's timeout. It is not evidence of a failed Lean declaration, and it is not a completed proof-bank acceptance run. An updated-head run must finish its compilation and axiom audit.

## Physical mass: confirmed job timeout

- Run: [46047919125](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46047919125).
- Job: [140671724888, Universal Lean implication and compiled axiom audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46047919125/job/140671724888).
- Workflow: `.github/workflows/physical-mass-kernel.yml`, job `lean`.
- First log timestamp: `2026-11-27T19:26:10.2180519Z`.
- Cancellation timestamp: `2026-11-27T20:01:23.2277493Z`.

The [check annotation](https://api.github.com/repos/larsbx/pisot-substitution-conjecture-research/check-runs/140671724888/annotations) explicitly states:

> The job has exceeded the maximum execution time of 35m0s

The log's only actual error marker is the cancellation. Before cancellation, the full build reached 9,242 of 9,250 jobs. All 18 new closure modules compiled successfully, as did both legacy consumers affected by extraction:

| Module | Successful build timestamp (UTC) |
| --- | --- |
| `GeometricFStrict` | 19:49:09 |
| `GeometricFPisot` | 19:50:38 |
| `BHThreeBandClosure` | 19:55:42 |
| `BHThreeBandBPA` | 19:56:17 |
| Last reported completed module, `NamedPositiveOverlap` | 20:00:35 |

The log includes tactic suggestions within successfully built modules; those are warnings, not failed proof commands. The final complete proof-bank audit was not reached, so this partial build receives no full-gate acceptance credit.

The job uploaded its three-file partial receipt as artifact [15228217837](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/46047919125/artifacts/15228217837). GitHub reported archive SHA-256 `0ae36afee89f6da42b20943dc24b2eadc5eb8535ff70414d88e38b301ca34515`.

## Narrow corrective change

Change only the physical-mass `lean` job's `timeout-minutes` from 35 to 180. It runs the same complete `./tools/check_lean.sh` as the existing 180-minute overlap gate. Keep every command, revision check, toolchain pin, audit requirement, artifact step, and other job timeout unchanged.

A dated append-only side-note records both interrupted runs and their limits. No theorem source, checker, required acceptance condition, or vendored code changes are part of this correction. No rerun, review action, commit, or publication was performed during this investigation.
