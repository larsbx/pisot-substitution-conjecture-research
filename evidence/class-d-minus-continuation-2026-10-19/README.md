# PR #290 continuation: unbounded guard family and validation repairs

Date: 2026-10-19. Parent: `b10e1137f0b17bc405721ae968e7af934fdc2e8c`.
Local compiler: Mojo 1.1.0 (8189361e); compiler telemetry and crash reporting
were disabled with `MODULAR_TELEMETRY_ENABLED=false` and
`MODULAR_CRASH_REPORTING_ENABLED=false` on every replay.

## Mathematical result and exact scope

The six-edge control extends symbolically to every integer k>=2. Guard rows
0 and 5 add identically to -7-u. For the even subfamily k=2t, every edge
individually has an integral parameter witness for every t>=1, although no
single pair works for the whole cycle. The canonical QX calculation checks
polynomial identities, including the closing edge and the individual witness
inequalities; it is not a finite k census. Full statements, offset table,
guards, witnesses, proof and remaining coverage gap are in section 12 of
`docs/p1b-class-d-minus-recurrent-carrier-2026-10-19.md`.

The new ledger node `MinusSixEdgeFamilyExclusion` has precisely that scope.
`MinusClassDPositiveBCycleSum` remains open. The conditional family BH node,
universal #139 and PSC are not established by this exclusion.

## Replays

From kernel/, using the installed repository environment:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run mojo run -I . tests/test_class_d_minus_cycle_family.mojo
pixi run mojo run -I . class_d_minus_cycle_family.mojo
pixi run mojo run -I . tests/test_class_d_minus_shared_cycles.mojo
pixi run mojo run -I . tests/test_class_d_minus_cycle_reduction.mojo
pixi run mojo run -I . tests/test_symbolic_line_empty_blocks.mojo
```

The archived local logs use the available compiler stated above. From root:

```sh
python -m pytest -o addopts='' -q tests/test_class_d_minus_shared_cycles.py
python -m pytest -q tests/test_claim_governance.py tests/test_show_your_work_policy.py tests/test_ledger_generation.py tests/test_review_policy.py tests/test_vendored_sync.py tests/test_proof_bank.py tests/test_check_manuscript_source.py tests/test_check_markdown_source.py
TLA_TOOLS=/path/to/tla2tools.jar bash proof/tla/check.sh
python tools/make_ledger.py --check
python tools/make_proof_bank.py --check
python tools/make_math_catalogue.py --check
python tools/check_manuscript_source.py
python tools/check_markdown_source.py
python tools/vendoring/check_vendored_sync.py
PYTHONPATH=tools python -m claim_governance.cli --root .
```

No earlier calibration artifacts were replaced. The exact 56-specimen
Mojo/Python agreement is preserved in the preceding repair's evidence folder;
its graph construction and classification are unchanged by this continuation.

## Executed validation

- Canonical family test/driver, supplied-cycle controls, conditional reduction
  and the repaired empty-block test all passed on the stated local compiler.
- `family-python-tests.log`: 12 passed, including independent k and even-k
  calibrations. This does not supply the unbounded quantifier.
- `policy-tests.log`: 84 passed, one skipped (the optional TLC mutation test
  did not receive TLA_TOOLS in that pytest invocation).
- `tla.log`: all 17 models passed in the separate explicit TLA_TOOLS replay.
- `governance.log`: generated surfaces, manuscript integrity, Markdown,
  vendoring and the full claim-governance audit pass.
- An additional broader Python invocation including source-check regression
  files exited 0 but left an empty output file; no test count or receipt is
  credited to it here. The recorded policy run and direct integrity checks
  above are the inspectable validation evidence.

## Baseline failures repaired

- The show-your-work regression had a malformed Python string, preventing
  collection. It now checks the actual git-diff argument fragment.
- The proof ladder's imported bridge status now uses the governed vocabulary.
- The existing empty-block Mojo test now emits a contract only after its
  mathematical assertions pass.
- The existing two-obstruction completion theorem is registered with two
  distinct open universal premises, plus its established mechanisms and
  imported density bridge. The new TLA+ model supplies both premises only as
  assumptions. Tests show that either one alone is insufficient and that
  the scoped minus CycleSum assumption establishes neither universal premise.
- The manuscript contained three byte-identical 183,857-byte copies of its
  tail. Two were injected immediately after `A1`, before a surviving dollar
  sign, breaking the corollary and its proof. Remove those two copies and
  restore `$'` at each location, yielding the two `A1$'$` expressions. Retain
  the third body, all unique theorem text and the archived PDF unchanged.
  `manuscript-reconstruction.json` pins original, repeated block and corrected
  hashes. The original is recoverable verbatim at the parent commit. This
  is a source repair, not an independent review of the manuscript's proofs.
- All ledger surfaces and the proof bank were regenerated from their sources.

## Validation limits

The pinned nightly environment remains unavailable: a fresh locked pixi
installation failed fetching `max-benchmark-26.6.0.dev2026090805-release.conda`
with a tunnel/connect error. See `pinned-environment-failure.log`. No pin was
changed and no pinned-compiler success is claimed. GitHub CI was still queued
at the last prepublication check; this packet does not waive CI or claim
independent human review.
