# Scoped class-D assembly audit

This packet reconciles main (including merged #293 and #296) with #290 at
3b16b5447aa9b3ecdecfdabb5033a381580f230e. The mathematical derivation and exact
scope are in `docs/class-d-assembly-audit-2026-10-21.md`.

## Results and authority

- Fresh locked-runtime `minus-complete.log` / `.exit`: all four disjoint
  residual regions, all 114 strip finite-prefix members, symbolic tails and
  graph checks, seed carrier, ranked descent and target geometry. Exit zero.
- `seed-cover.log`: all-child proof and its coarse-region/removed-target
  refusal controls. Its two intentional unresolved-obligation lines are
  negative tests; the final contract and claim receipts are reached.
- `plus-boundary.log`: full symbolic a>=7 plus b=0 tail, all a=0..6 and full
  directed support checks at 7,8, including empty-run and damaged-edge controls.
- `assembly.log`: fresh native candidate consumes both complete receipts and
  replays plus b=0. Its marker explicitly retains `integration=pending` and
  `universal_139=open`. It uses the inherited large-r theorem at its exact
  scope, not an inferred proof from component counts.
- The hour-long plus positive-b aggregate is **reused**, not rerun. The exact
  source revision is 53a4021c0e534958c8088ff82f136913d3f08df8. All 47 files in
  its local import closure, its lock, immutable log and zero process exit
  match. Original component acceptance is unchanged. See `manifest.json`
  and `provenance-assembly.json`.
- `assembly-test.log` checks exact polynomial inverse and lattice identities,
  successful receipt assembly, omission/duplicate refusal and the difference
  between zero offset and equal-letter coincidence. The initial compiler
  aliasing refusal is retained separately, not credited as a pass.
- `seed-calibration.json` and `strip-calibration.json` are fresh independent
  Fraction/Q(beta) calibration with native receipt agreement. They do not
  supply a universal quantifier.
- `independent-tests.log`: 38 passed, one optional TLC mutation test skipped;
  includes complete independent plus/minus boundary oracles, the minus seed
  proof calibration, strip controls, certificate agreement and ledger tests.
- `final-tests.log`: 34 passed, one optional TLC mutation test skipped, using
  the fresh calibration reports; includes provenance refusal controls,
  generated ledger, workflow and research-evidence checks.
- `assembly-governance-tests.log`: 21 passed, one optional mutation test
  skipped after strengthening missing-source/evidence refusal controls.
- `console-pytest-collection.log`: the actual pytest console entrypoint now
  collects both oracle-importing modules successfully (8 tests). This
  reproduces the launch mode that failed in historical CI.
- `tla-final.log`: all 18 models pass, including the integration-assumed model
  and the two-obstruction firewall. The Python optional mutation test skip is
  not used as a substitute for these separately executed TLA models.
- `provenance-final.log`: generated ledger/proof-bank/catalogue, vendoring,
  source integrity, polyglot rendering, hit-witness provenance and full claim
  governance pass. No vendored package or environment pin changes.

Native supplementary sign, chamber partition, ordered child sweep,
empty-block and full symbolic-line regression logs each have a matching
`.exit` file. Only an existing zero exit with its reached contract is credited;
no partial running log is a successful receipt.

## Locked environment and CI limitations

`runtime-identity.json` records the compiler/runtime archive hashes matching
unchanged `kernel/pixi.lock`, the actual compiler binary and TLA jar. The
initial urllib redirect refusal is in `runtime-bootstrap.log`; curl obtains
the same pinned archives, whose hashes are checked before extraction. Actual
execution is Mojo 1.1.0.dev2026090805 (34562fa1), telemetry/crash reporting off.

`pixi-install.log` / `.exit` records this session's failed **full** locked
installation: a proxy tunnel failure fetching locked starlette. It is not
relabeled as an install success. The successful native runs use the minimal
hash-verified compiler/runtime instead.

`historical-ci.json` records a different fact: GitHub run 39352929916, job
118401083796, successfully installed the full locked environment on old test
merge d4806dc, then failed full verification on the inherited 21/18 symbolic
line pin and the pytest console import path. The pin repair is merged #293;
this contribution fixes the import path. That historical setup success is
not current-head CI acceptance. Cancelled checks are not successes.

The full repository Mojo suite, all exhaustive censuses, Lean build and full
Python suite are not newly credited by this scoped packet. Current combined
CI acceptance remains open. Independent human review remains pending and is
not replaced by this audit. Class A/C, #138, #139, #84/G1 and PSC are not
promoted. The conditional class-D ledger explicitly depends on the open
integration gate.

## Replay

Run from the repository root with the unchanged locked environment available:

```sh
python tools/check_class_d_assembly_evidence.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_d_assembly.mojo
pixi run --locked mojo run -I . tests/test_class_d_minus_boundary_strips.mojo
pixi run --locked mojo run -I . tests/test_class_d_minus_seed_cover.mojo
pixi run --locked mojo run -I . class_d_assembly.mojo ../evidence/class-d-chamber-validation-2026-10-20/aggregate.log ../evidence/class-d-assembly-audit-2026-10-21/minus-complete.log
```

The dedicated `.github/workflows/class-d-assembly.yml` runs these under the
full locked environment, calibrates a freshly produced minus log and keeps
failure artifacts. It also checks the immutable plus import closure. Existing
full repository CI requirements remain in force.

For a minimal local replay, bootstrap the two unchanged locked archives with
`evidence/class-d-chamber-continuation-2026-10-19/bootstrap-pinned-mojo.py` and
set MODULAR_MAX_PACKAGE_ROOT, MODULAR_MOJO_MAX_PACKAGE_ROOT and
MODULAR_MOJO_MAX_IMPORT_PATH to its root, root and root/lib/mojo. Call its
bin/mojo directly in the commands above, with telemetry/crash reporting off.
This is explicitly the minimal-runtime replay, not a complete Pixi install.

The packet manifest binds native evidence and replay source bytes. The packet
SHA256SUMS additionally covers the inspection/replay record. Provenance tooling
never prints a mathematical certificate or bypasses component acceptance.
