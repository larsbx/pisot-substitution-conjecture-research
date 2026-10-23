# Class-A gap four, residue rays — 2026-10-23

Written argument, scope and non-claims: `docs/class-a-d4-rays-2026-10-23.md`.
Boundary hitting on `(n+4,n,n+1)` for every `n>=0` and on `(n+4,n,n-1)` for
every `n>=3`, each the line's whole PIP domain. Eight residue rays `n = 4l + r`
are certified by the generic residue-ray certificate from their floors
(plus 24/21/22/15, minus 24/25/22/23). Every smaller `n` is an exact complete
graph.

- `driver.log` / `.exit`: `kernel/class_a_residue_ray.mojo certify 4 EPS R N0`
  for the eight rays.
- `survey.log` / `.exit`: `survey 4 1 30` and `survey 4 -1 30`.
- `native-tests.log` / `.exit`: `kernel/tests/test_class_a_residue_rays.mojo`
  over all 18 tabulated rays. It surveys every line's domain below the floor
  from `q=0` (including the d=4 plus member `n=0`), replays two members per
  ray, and runs the per-ray negative controls.
- `oracle.jsonl` / `.exit`: `oracles/python/class_a_carrier_closure.py N0 --ray 4,EPS,R`,
  one line per ray; every count equals the Mojo count.
- `python-tests.log` / `.exit`: `tests/test_class_a_residue_rays.py` and
  `tests/test_class_a_d2_plus_ray_carrier.py`.
- `generator.log`, `descent-table-d4{p,m}-r*.json`:
  `oracles/python/class_a_descent_table.py --ray 4,EPS,R` regenerating
  `kernel/psc/class_a_ray_d4p.mojo` and `class_a_ray_d4m.mojo` byte-identically
  from the exports (`GRAPHS/` is the export directory). The generator is not
  evidence.
- `graph-exports-sha256.txt`: digests of `export 4 EPS N`, plus n=1..55 and
  minus n=3..47. `graph-d4p-n24.log` is retained.
- `mojo-version.txt`, `manifest.json`: runtime, base commit, source digests,
  per-ray counts and non-claims.

All logs are unedited combined stdout/stderr; `.exit` files are exit codes.
Local execution used the lock-matched compiler in `mojo-version.txt`; this is
not a CI receipt.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_residue_rays.mojo)
(cd kernel && pixi run --locked mojo run -I . class_a_residue_ray.mojo certify 4 -1 1 25)
python oracles/python/class_a_carrier_closure.py 24 --ray 4,1,0
python -m pytest -q tests/test_class_a_residue_rays.py
(cd evidence/class-a-d4-rays-2026-10-23 && sha256sum -c SHA256SUMS)
```

`SHA256SUMS` covers every file in this packet except itself.
