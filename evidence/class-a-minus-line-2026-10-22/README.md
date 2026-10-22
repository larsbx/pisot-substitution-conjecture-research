# Class-A minus line closure and descent — 2026-10-22

Written argument, scope and non-claims: `docs/class-a-minus-line-2026-10-22.md`.
The result is boundary hitting on the class-A line `(p,q,r)=(n+1,n,n-1)` for
every integer `n>=1`: the 104-row typed carrier is forward closed for `n>=8`
and carries a 176-piece affine potential that strictly decreases along 265
chosen child occurrences for `n>=8` (first-hit depth `<= 2n+11`); `n=1..7` are
exact complete-graph certificates. Gap `d>=2`, the other class-A regions, the
class-C residual and universal #139 remain open. Independent human review is
pending.

- `native-tests.log` / `.exit`: `kernel/tests/test_class_a_minus_line.mojo`
  (line identities and actual incidence, closure at `n0=8,10`, descent at
  `n0=8`, refusal controls, complete graphs `n=1..7`, carrier = graph label set
  at `n=5,6,7,8,18`, differential replay of every chosen occurrence at `n=8,11`).
- `driver.log`, `survey.log` / `.exit`: `kernel/class_a_minus_line.mojo certify 8`
  and `survey 24`.
- `oracle.json` / `.stderr` / `.exit`: the independent Python verifier
  (`oracles/python/class_a_carrier_closure.py 8 --line minus`); its counts
  equal the Mojo counts.
- `python-tests.log` / `.exit`: `tests/test_class_a_minus_line.py` and the
  plus-line `tests/test_class_a_carrier_closure.py`.
- `rows-generator.log`, `generator.log`, `descent-table.json` / `.exit`: the
  output of `oracles/python/class_a_descent_table.py --line minus` on the
  exports `n=5..24` (rows) and `n=8..24` (pieces, descents);
  `kernel/psc/class_a_minus_carrier.mojo` and
  `kernel/psc/class_a_minus_descent_data.mojo` are byte-identical to its
  renderings. The generator is not evidence; the two verifiers are.
- `graph-exports-sha256.txt`, `graph-n8.log`: digests of the exact exports
  `n=4..24` written by `kernel/class_a_minus_line.mojo export N`; `n=8` retained.
- `plus-native-tests.log` / `.exit`, `plus-regression.txt`: the plus-line test
  and byte comparisons showing the line-parametric refactor reproduces the
  archived #310 native log, oracle JSON and generator output exactly.
- `mojo-version.txt`, `manifest.json`: runtime identity, base commit, source
  digests, counts and non-claims.

All logs are unedited combined stdout/stderr; `.exit` files are process exit
codes. Local execution used the lock-matched `Mojo 1.1.0.dev2026090805
(34562fa1)`; this is not a CI receipt.

Replay from the repository root:

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_minus_line.mojo)
(cd kernel && pixi run --locked mojo run -I . class_a_minus_line.mojo certify 8)
python oracles/python/class_a_carrier_closure.py 8 --line minus
python -m pytest -q tests/test_class_a_minus_line.py
sha256sum -c evidence/class-a-minus-line-2026-10-22/SHA256SUMS
```

`SHA256SUMS` covers every file in this packet except itself.
