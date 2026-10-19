# Shared parameters do not replace seed reachability

Parent: `5e9391d43c10f7fcf969db0e16fecb6108a84927`. Date: 2026-10-19.

## Exact result

For every integer k>=2, set a=2k-1,b=1. The integral states
U_k=(y,c,-2k,4k,-3k) and its mirror form a two-cycle with actual indices
(4k+4,6k+4) and their reverse, for the same substitution. Their sums are -k,k.
The symbolic Mojo certificate verifies PIP, both occurrence identities, strict
interior margins, and normalized displacement -1/2<t<0 throughout k>=2.
It refuses any proof that raises the threshold. This is an unbounded symbolic
statement; no finite search supplies its quantifier.

This refutes the stronger seed-free CycleSum claim. It does not refute the
stated seed-qualified CycleSum-. “Real-interior formal” does not assert legal
tiling occurrence, full non-unit realization or seed reachability. The
complete three-specimen seed graphs omit these pairs; uniform nonreachability
is still unproved. Unknown higher-sum seed labels remain failures in the
canonical recurrent diagnostic.

The derivation and general cyclic scalar reconstruction are in section 13 of
`docs/p1b-class-d-minus-recurrent-carrier-2026-10-19.md`. The literature gate
records the stop on universal formal-cycle exclusion and the redirection to a
seed-preserved constraint.

## Executed evidence and replay

Local compiler: Mojo 1.1.0 (8189361e), with telemetry and crash reporting off.
Use the repository environment from kernel/:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run mojo run -I . tests/test_class_d_minus_high_sum_cycles.mojo
pixi run mojo run -I . class_d_minus_high_sum_cycles.mojo > ../high-sum-driver.log
```

From the repository root:

```sh
python oracles/python/class_d_minus_high_sum_cycles.py --mojo-log high-sum-driver.log > high-sum.json
CLASS_D_HIGH_SUM_REPORT=high-sum.json python -m pytest -q tests/test_class_d_minus_high_sum_cycles.py
python tools/make_ledger.py --check
python tools/make_proof_bank.py --check
PYTHONPATH=tools python -m claim_governance.cli --root .
TLA_TOOLS=/path/to/tla2tools.jar bash proof/tla/check.sh
```

`high-sum-test.log` includes the unbounded symbolic receipt, finite occurrence
replays, three complete seed nonmembership checks and explicit cap refusal.
`high-sum-driver.log` is compared by the independently implemented exact
Q(beta) oracle; `python-calibration.json` preserves its states, occurrences
and membership outcomes. All three graphs have 139 vertices. The calibration
samples are k=2,3,8, not a universal seed exclusion. The CLI emits its JSON
before checking agreement, so even disagreement preserves counterexample
replay data. CI always uploads its logs and JSON.

The recorded focused Python run has 90 passed and one optional TLC mutation
check skipped because TLA_TOOLS was not supplied to pytest. All 17 TLA+
models pass in the separate explicit replay. Generated surfaces, manuscript,
Markdown, vendoring and the full governance audit pass (`governance.log`).

The new governed claim is `MinusHighSumFormalCycleRay`. Tests keep CycleSum-,
minus boundary hitting, universal #139 and PSC unestablished in the open
ledger model. Existing evidence packets are preserved unchanged.

## Validation limits

The pinned nightly replay remains outstanding after the previously recorded
pixi package tunnel failure in the preceding continuation packet. No pin was
changed. GitHub workflows remained queued when checked for this work.
Available local compiler receipts are not represented as pinned-toolchain CI
or independent human review. The arithmetic/geometry certificate proves the
formal ray only, not the occurrence of these states in any legal seed patch.
