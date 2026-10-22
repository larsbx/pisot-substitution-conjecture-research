# PR #290 diagnostic repair: executed evidence

Scope: minus class-D a>=2,b>=1. Parent PR head:
`760bc3b32e03eecf0f7c7839f8aceb975d2152cd`. The conditional reduction and
finite calibration are different objects. CycleSum-, #139/#84 and PSC are open.

## Passed executions

- Canonical Mojo **1.1.0 (8189361e)**: recurrent-support test and 56-specimen
  driver, conditional cycle-reduction test and driver, shared-parameter test
  and driver, and the affected positive-b geometry regression.
- Exact grid: 2<=a<=8,1<=b<=8, cap 20,000 states. Every recurrent label and
  classification agrees with the independent Q(beta) Python oracle. The graphs
  have 137/139 states and 127/129 recurrent vertices; no unexplained labels,
  no finite CycleSum violations, and no recurrent seed label outside the carrier.
- The four exceptional formal cycles and their exits are checked separately
  at a=2,b=1,2. They are not reported as seed-reachable counterexamples.
- Conditional superset: 1,971 states; 145 recurrent = 131 carrier + 2 zero
  targets + 8 boundary-only + 4 exceptions. Eight exceptional occurrence edges
  verified. The noncarrier zero targets are (x,x,0) and (c,x,0); only the first
  is a terminal coincidence. The graph remains conditional on CycleSum-.
- Six-edge shared-parameter control: all individual edges have integer
  witnesses; combining guard rows 0 and 5 gives -7-u<0 for u>=0. General
  checked Farkas multipliers are also emitted. A genuine U/Ubar cycle is retained.
- Ten targeted Python tests pass. They reuse this freshly executed grid JSON
  and compare all labels against the canonical log; standalone tests recompute
  the grid. Forced carrier omission exercises counterexample replay without
  claiming that the actual carrier omitted the label.
- All 16 TLA+ models pass, including `MCLedgerMinusCycleSumAssumed`. Assuming
  CycleSum establishes only the family result, not universal #139, #84, G1 or PSC.
- Focused ledger-generation/review-policy/vendoring tests: 23 pass, one skip.
  Generated ledgers, mathematical catalogue, proof bank, vendoring,
  Markdown integrity and `git diff --check` pass.

## Validation limits and preserved failures

The repository-pinned pixi environment could not be installed: fetching
`https://conda.anaconda.org/conda-forge/linux-64/libfreetype-2.14.3-ha770c72_2.conda`
failed after three retries with a tunnel/connect error. The local results above
use installed Mojo 1.1.0, **not** the pinned 1.1.0.dev2026090805. No pinned replay
or whole Mojo-suite success is claimed.

A first tool invocation was stopped by automatic approval review because of
possible compiler telemetry. Subsequent executions used both
`MODULAR_TELEMETRY_ENABLED=false` and `MODULAR_CRASH_REPORTING_ENABLED=false`,
as documented in Modular's own
[bazel configuration](https://github.com/modular/modular/blob/main/bazel/internal/common.bazelrc).

The untouched parent was checked in a detached worktree. Its preserved logs
reproduce these repository blockers:

- manuscript source checker rejects `\\end{document}` at line 1357;
- proof-ladder DensityToPDSBridge status anchor is unrecognized;
- `test_symbolic_line_empty_blocks.mojo` lacks a contract declaration;
- claim-map regression has an unregistered two-obstruction completion row;
- `tests/test_show_your_work_policy.py:57` has an unterminated string literal.

The parent's stale proof-bank pin was regenerated because this repair changes
the governed ledger; the current proof bank now passes its check. The other
baseline failures are not waived. PR integration must not be represented as a
fully green repository validation or an unconditional minus-BH proof.

## Replay

See `docs/p1b-class-d-minus-recurrent-carrier-2026-10-19.md` §11 for canonical
commands. `recurrent-mojo.log` and `recurrent-support.json` expose the complete
finite classifications. `recurrent-tests.log` contains the intentional
`NEGATIVE_CONTROL forced_carrier_omission` followed by exact seed/cycle
occurrence replay. The conditional and shared-cycle logs expose their receipts
and exact constraints. `source-sha256.json` binds the mathematical code tested.
