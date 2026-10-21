# Complete minus residual and Issue #139 scope update

Parent: PR #290 at `44dceb18f1a377010981262aa5f711f0be3d0064`.
Date: 2026-10-20 UTC.

## Mathematical result

The two omitted strips certify using the unchanged exact line engine:

| a | n=b-1 threshold | Tail vertices | Exact finite prefix | Graph checks |
| --- | ---: | ---: | --- | --- |
| 0 | 42 | 140 | every n=0..41 PIP and hitting | 42,47 |
| 1 | 72 | 137 | every n=0..71 PIP and hitting | 72,77 |

The complete invocation covers b=0, a=0/b>=1, a=1/b>=1 and a>=2/b>=1,
including all seeds/children and exact ranked target geometry. The native
aggregate marker therefore covers all a,b>=0 in the minus residual. Together
with the existing r>=q-1 theorem and the exact residual parameter map, this
proves boundary hitting for every PIP minus class-D member p=q-1.
Universal Issue #139, #84 and PSC remain open. See the derivation in
`docs/p1b-minus-boundary-strips-2026-10-20.md`.

## Replay and evidence

Using the repository's full pinned environment from `kernel/`:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run --locked mojo run -I . tests/test_class_d_minus_boundary_strips.mojo
pixi run --locked mojo run -I . class_d_minus_complete.mojo
```

The regression already calls the complete native aggregate; running the
standalone driver is an alternative replay, not needed to repeat the proof.
For one strip alone use `class_d_minus_boundary_strips.mojo 0` or `1`; the
single-strip mode never emits the complete-quadrant marker.

From the repository root:

```sh
python oracles/python/class_d_minus_boundary_strips.py --mojo-log evidence/issue139-minus-strips-2026-10-20/complete-test.log > strip-calibration.json
CLASS_D_MINUS_STRIPS_REPORT=strip-calibration.json CLASS_D_MINUS_COMPLETE_LOG=evidence/issue139-minus-strips-2026-10-20/complete-test.log python -m pytest -q tests/test_class_d_minus_boundary_strips.py tests/test_ledger_generation.py
bash tools/verify_all.sh provenance
TLA_TOOLS=/path/to/tla2tools.jar bash proof/tla/check.sh
```

- `strip-0.log`, `strip-1.log`: complete individual line invocations.
- `complete-test.log`: final-source native all-component aggregate and reached
  contract/claim receipts. The earlier identical computation without the
  three added claim-label calls is `complete-before-claim-labels.log`.
- `pinned-seed-cover-test.log`: the preceding uniform seed proof also passes
  on the locked compiler version, including its refusal controls.
- `pinned-spine-test.log`: exact rank-spine partition after source-compatibility
  repairs. `inherited-spine-compile-refusal.log` preserves the initial failure.
- `python-calibration.json`: six independent exact Q(beta) graphs at a=0,1,
  b=1,2,73; finite calibration only. Every vertex is boundary-hitting; tail
  vertex counts agree with the canonical symbolic proof.
- `python-tests.log`: new receipt-completeness/calibration and ledger tests.
  Missing/duplicate strips, graph caps and invalid selectors refuse.
- `tla.log`: all 17 models, including firewalls keeping universal hitting,
  aligned coincidence and PSC unestablished in the open model.
- `governance.log`: generated surfaces, vendoring and source/claim audit.
- `source-sha256.json`, `runtime-files.json`, `run-context.json`: identities
  and execution provenance. Historical evidence packets remain unchanged.

## Compiler/runtime identity and limitations

Actual execution used Mojo 1.1.0.dev2026090805 (34562fa1) from the minimal
runtime provisioned for #293. Both archive SHA-256 values equal the unchanged
lockfile entries:

- compiler: `0d71889abb0887e2fa8a556c1081af4026034cdf98d27ad05b57cb096d7ad4f6`;
- mojo-python: `113c7d202236f943c91fdcb115f0a278e9c6027e1b7783bbc8b9a2076bb43838`.

`runtime-files.json` verifies the installed compiler, standard library and
three Modular shared libraries against the archive. Replay with this minimal
environment sets MODULAR_MAX_PACKAGE_ROOT, MODULAR_MOJO_MAX_PACKAGE_ROOT and
MODULAR_MOJO_MAX_IMPORT_PATH to its root and lib/mojo, respectively, and calls
bin/mojo directly. Telemetry and crash reporting were disabled throughout.
The immutable bootstrap recipe is in #293 commit
`e17aef51f6773a97d04201d73b77a4354651b5bb`, at
`evidence/class-d-chamber-continuation-2026-10-19/bootstrap-pinned-mojo.py`.

This is not a complete successful Pixi installation or a GitHub CI receipt.
Those integration gates and independent human review remain pending. None
of #293's source changes is imported for these proofs. Its plus result stays
separate; this packet does not promote universal #139 or general PSC.
