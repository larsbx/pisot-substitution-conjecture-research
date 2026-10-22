# Class-A carrier closure and descent — 2026-10-22

Written argument, scope and non-claims:
`docs/class-a-carrier-closure-2026-10-22.md`. The result is boundary hitting
on the class-A line `(p,q,r)=(n+1,n,n+1)` for every integer `n>=4`: the
89-row typed carrier is forward closed for `n>=5` and carries an affine
potential that strictly decreases along chosen child occurrences for `n>=8`
(first-hit depth `<= 2n+9`); `n=4..7` are exact finite certificates. Other
class-A regions, the class-C residual and universal #139 remain open.
Independent human review is pending.

- `native-tests.log` / `.exit`: the canonical Mojo regression
  (`kernel/tests/test_class_a_carrier_closure.mojo`): sign-decision controls,
  closure at `n0=8` and `n0=5`, descent at `n0=8`, refusal controls, exact
  finite certificates `n=4..7`, differential replay of every chosen child
  occurrence against the exact Perron-field engine at `n=8,11`.
- `driver.log` / `.exit`: `kernel/class_a_carrier_closure.mojo 8`.
- `oracle.json` / `.stderr` / `.exit`: the independent Python verifier
  (`oracles/python/class_a_carrier_closure.py 8`); its counts equal the Mojo
  counts line by line.
- `python-tests.log` / `.exit`: `tests/test_class_a_carrier_closure.py` and
  the existing typed-carrier structural tests.
- `descent-table.json`, `generator.log` / `.exit`: the output of
  `oracles/python/class_a_descent_table.py` on the exact graph exports
  `n=8..24`; `kernel/psc/class_a_descent_data.mojo` is byte-identical to the
  generator's `--mojo` rendering. The generator is not evidence; the two
  verifiers are.
- `graph-exports-sha256.txt`: digests of the exact exports `graph-n4..24.log`
  produced by `kernel/class_a_run_index.mojo export N` (unchanged exporter);
  `graph-n8.log` is retained here, `n=4` and `n=18` are archived in
  `evidence/class-a-run-index-2026-10-21/`. The other exports are reproduced
  by the exporter.
- `*.txt`: snapshots of every new or changed source, test, oracle, workflow
  and note. `kernel-source-sha256.json`: every tracked kernel source at
  execution. `manifest.json`: new-source digests, the reused lock-matched
  runtime identity, counts and explicit non-claims.

All logs are unedited combined stdout/stderr; `.exit` files are process exit
codes. Local execution used the lock-matched `Mojo 1.1.0.dev2026090805
(34562fa1)` already identified by the accepted class-D receipts; this is not
a fresh full-Pixi or CI receipt. The dedicated workflow
`.github/workflows/class-a-carrier-closure.yml` produces locked receipts.

Replay from the repository root:

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_carrier_closure.mojo)
(cd kernel && pixi run --locked mojo run -I . class_a_carrier_closure.mojo 8)
python oracles/python/class_a_carrier_closure.py 8
python -m pytest -q tests/test_class_a_carrier_closure.py
sha256sum -c evidence/class-a-carrier-closure-2026-10-22/SHA256SUMS
```

`SHA256SUMS` covers every file in this packet except itself. No accepted
class-D certificate or receipt is modified.
