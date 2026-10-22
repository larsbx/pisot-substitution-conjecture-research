# Class-A d=2 plus line, residue rays — 2026-10-22

Written argument, scope and non-claims: `docs/class-a-d2-plus-rays-2026-10-22.md`.
Boundary hitting on the class-A line `(n+2,n,n+1)` for every `n>=1`: the two
residue rays `n = 2l + r` certified by the generic certificate of
`docs/class-a-residue-rays-2026-10-22.md` (even floor 14, odd floor 13), and
an exact complete graph for every smaller `n`.

- `driver.log`: `kernel/class_a_residue_ray.mojo certify 2 1 R N0` for both rays.
- `survey.log` / `.exit`: `survey 2 1 30` (exact complete graphs n=1..30).
- `native-tests.log` / `.exit`: `kernel/tests/test_class_a_residue_rays.mojo`
  over all ten tabulated rays (the eight of #321 unchanged, plus these two).
- `oracle.jsonl` / `.exit`: `oracles/python/class_a_carrier_closure.py N0 --ray 2,1,R`,
  one line per ray; every closure and descent count equals the Mojo count.
- `python-tests.log` / `.exit`: `tests/test_class_a_residue_rays.py` and
  `tests/test_class_a_d2_plus_ray_carrier.py` (ray rows = the independent #312
  Fraction-field profiles at n=8,9,12,13).
- `generator.log`, `descent-table-d2p-r*.json`: `oracles/python/class_a_descent_table.py
  --ray 2,1,R` regenerating `kernel/psc/class_a_ray_d2p.mojo` byte-identically
  from the exports (`GRAPHS/g2p`). The generator is not evidence.
- `graph-exports-sha256.txt`: digests of `export 2 1 N`, n=4..39;
  `graph-d2p-n14.log` retained.
- `mojo-version.txt`, `manifest.json`: runtime, base commit, source digests,
  per-ray counts and non-claims.

All logs are unedited combined stdout/stderr; `.exit` files are exit codes.
Local execution used the lock-matched compiler in `mojo-version.txt`; this is
not a CI receipt.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_residue_rays.mojo)
(cd kernel && pixi run --locked mojo run -I . class_a_residue_ray.mojo certify 2 1 0 14)
python oracles/python/class_a_carrier_closure.py 13 --ray 2,1,1
python -m pytest -q tests/test_class_a_residue_rays.py tests/test_class_a_d2_plus_ray_carrier.py
(cd evidence/class-a-d2-plus-rays-2026-10-22 && sha256sum -c SHA256SUMS)
```

`SHA256SUMS` covers every file in this packet except itself.
