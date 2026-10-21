# Class-D integration acceptance — 2026-10-21

PR [#290](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/290)
merged as `4996d21f18b24f4e45f6b30a7dbf92901cd35bd8` at 06:53:12 UTC.
The final general census completed at 06:57:25 UTC. At the recorded head
`a9457d9a08e971d57a635e68086a558fcff88e11`, all **64 check runs succeed**.
The head, tested PR merge `31b5d1e73f7becd34a4ecfe99eb6df186a88fafa` and
main merge all have tree `c325aa5345e1f49b2fb50b37565bd2902104aab7`.
`tested-merge.commit` is the raw Git commit object content; its Git object ID
and tree are verified without requiring the ephemeral PR merge ref.

`check-runs.json` is the full normalized GitHub response from
`GET /repos/larsbx/pisot-substitution-conjecture-research/commits/a9457d9a08e971d57a635e68086a558fcff88e11/check-runs?per_page=100`.
`repository-jobs.json` and `component-jobs.json` preserve job steps from the
corresponding workflow runs. Each numeric `.log.gz` contains the unedited
decoded GitHub job log, losslessly compressed with gzip timestamp zero.
The manifest pins both decompressed log hashes and every accepted component
source/import, runtime lock, independent calibration and workflow file.
SHA256SUMS also pins each actual packet file.

| Job | Receipt |
| --- | --- |
| [119058204076](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452540/job/119058204076) | Scoped assembly, full minus and plus b=0, independent Q(beta)/Fraction calibration, provenance/governance; full locked Pixi setup |
| [119058204598](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452644/job/119058204598) | Complete plus positive-b chambers: six cores, 73 strips, six interfaces, 952 finite-prefix obligations, locked setup |
| [119058204005](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452521/job/119058204005) | Second complete plus positive-b aggregate, obstruction controls and locked setup |
| [119058204237](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452521/job/119058204237) | Complete minus four-region aggregate, locked setup |
| [119058204741](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452554/job/119058204741) | Conditional cycle controls, uniform seed carrier, complete minus strips and independent calibration; higher-sum formal-cycle controls retained |
| [119058204815](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452563/job/119058204815) | Full Python suite: 649 passed, two skipped, one warning |
| [119058204742](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452563/job/119058204742) | Full native Mojo suite, claim coverage, 10 certificate checks, standing census |
| [119058203980](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452641/job/119058203980) | Locked exact-kernels verification: 16 checks run, two skipped; separate Lean/TLA jobs in the complete snapshot pass |
| [119058204966](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/39550452563/job/119058204966) | Last general census: all 4,554 specimens complete, capped=0, every committed standing failure label agrees |

Replay the provenance audit from a full checkout:

```sh
python tools/check_class_d_assembly_evidence.py
python tools/check_class_d_integration_ci.py
python -m pytest -q tests/test_class_d_integration_ci.py tests/test_ledger_generation.py tests/test_recorded_data_integrity.py
```

These are **CI provenance records**, not a new mathematical certificate.
The exact mathematical authority and replay commands remain in
`docs/class-d-assembly-audit-2026-10-21.md` and the native component workflows.
Native assembly output deliberately remains `integration=pending`; the
separate completed CI event supplies acceptance without rewriting old output.
The earlier pending manifests and failed/interrupted logs remain historical.

This supports project progression for the exact determinant-two class-D
swap-seed graph scope. Offset-zero hitting does not assert equal-letter
coincidence. Independent human review, remaining class-A/C regions, universal
Issue #139, #138/#84, G1 and general PSC are not discharged. Local full Pixi
still encounters a proxy download failure; the successful full GitHub locked
installs establish the CI environment acceptance, not a successful local install.

Local governance/ledger/proof-bank regression: 83 passed, one optional TLC
mutation test skipped; the strengthened CI provenance regression separately
passes all eight cases. All 18 TLA model outcomes match their expectations.
See `local-*.log` for these follow-up receipts.
