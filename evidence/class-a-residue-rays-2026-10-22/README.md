# Class-A residue rays — 2026-10-22

Written argument, scope and non-claims: `docs/class-a-residue-rays-2026-10-22.md`.
Boundary hitting on the class-A lines `(n+2,n,n-1)` (n>=2), `(n+3,n,n-1)`
(n>=2) and `(n+3,n,n+1)` (n>=1): eight residue rays `n = d l + r`, each with
an `l`-affine typed carrier proved forward closed and an `l`-affine potential
proved strictly descending from the ray's floor (14..20), and an exact
complete graph for every smaller `n`. Other gaps, the `d=2` plus line, the
class-C residual and universal #139 remain open. Independent human review
is pending.

- `native-tests.log` / `.exit`: `kernel/tests/test_class_a_residue_rays.mojo`
  (division helpers, ray refusals, the uniform certificate on every tabulated
  ray, complete graphs below every floor, carrier = graph label set and
  differential replay at the first two members, per-ray negative controls).
- `driver.log`: `kernel/class_a_residue_ray.mojo certify D EPS R N0` for the
  eight rays; `survey.log` / `.exit`: `survey D EPS 30` for the three lines
  (88 exact complete graphs, n<=30).
- `oracle.jsonl` / `.exit`: the independent Python verifier
  (`oracles/python/class_a_carrier_closure.py N0 --ray D,EPS,R`), one line per
  ray; its closure and descent counts equal the Mojo counts.
- `python-tests.log` / `.exit`: `tests/test_class_a_residue_rays.py` and the
  two gap-one Python tests.
- `generator.log`, `descent-table-*.json`: `oracles/python/class_a_descent_table.py
  --ray D,EPS,R` (commands logged with `GRAPHS/` for the export directory)
  regenerating `kernel/psc/class_a_ray_d2m.mojo`, `class_a_ray_d3m.mojo` and
  `class_a_ray_d3p.mojo` byte-identically from the exports. The generator is
  not evidence; the two verifiers are.
- `graph-exports-sha256.txt`: digests of the exports (`class_a_residue_ray.mojo
  export D EPS N`): `g2m` = (n+2,n,n-1) n=5..34, `g3m` = (n+3,n,n-1) n=4..35,
  `g3p` = (n+3,n,n+1) n=4..35; `graph-d2m-n14.log` retained.
- `gap-one-plus-tests.log`, `gap-one-minus-tests.log` / `.exit`: the gap-one
  tests under the generalized certificate; byte-identical (blank lines aside)
  to the native logs archived in `evidence/class-a-carrier-closure-2026-10-22/`
  and `evidence/class-a-minus-line-2026-10-22/`.
- `mojo-version.txt`, `manifest.json`: runtime identity, base commit, source
  digests, per-ray results and non-claims.

All logs are unedited combined stdout/stderr; `.exit` files are process exit
codes. Local execution used the lock-matched `Mojo 1.1.0.dev2026090805
(34562fa1)`; this is not a CI receipt.

Replay from the repository root:

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_residue_rays.mojo)
python oracles/python/class_a_carrier_closure.py 19 --ray 3,-1,1
python -m pytest -q tests/test_class_a_residue_rays.py
(cd evidence/class-a-residue-rays-2026-10-22 && sha256sum -c SHA256SUMS)
```

`SHA256SUMS` covers every file in this packet except itself.
