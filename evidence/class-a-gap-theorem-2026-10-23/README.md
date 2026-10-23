# Class-A gaps d>=5, both signs: boundary hitting for every n >= 5d — 2026-10-23

Written argument, scope and non-claims: `docs/class-a-gap-theorem-2026-10-23.md`;
lemmas: `docs/class-a-gap-uniform-certificate-design-2026-10-23.md`. On every
class-A line `(n+d, n, n+eps)` of gap `d >= 5` and either sign, every vertex of
the complete canonical swap-seed graph has an offset-zero descendant, for every
member `n = d l + r` with `l >= 5`. Eighteen residue regimes certify closure and
descent uniformly in the gap; four minus finite gaps are ray certificates on the
regime tables; seven plus residues carry their own ray tables; three members
below ray floors are exact complete graphs. The strip `n < 5d` is not covered.

- `theorem.log` / `.exit`: `kernel/class_a_gap_theorem.mojo certify-all 5`, the
  whole chain for both signs (`CLASS_A_GAP_THEOREM` receipts).
- `cover.log` / `.exit`: `class_a_gap_theorem.mojo cover EPS 16`, the covering
  regime or ray of every residue of every gap `5 <= d <= 16` and the eventual
  pattern (`regimes_cover_every_residue_from_d>=7` minus, `>=11` plus).
- `closure-floors.log` / `.exit`: `class_a_gap_uniform.mojo floor-all 5 24`,
  the least gap floor from which each regime closure certifies, with the ray
  closure on the regime tables for the gaps below it.
- `descent-floors.log` / `.exit`: `class_a_gap_uniform.mojo descent-floor EPS KIND J 5 24`
  for every regime; every descent certifies from its fitted floor.
- `exceptional-rays.log` / `.exit`: `class_a_residue_ray.mojo certify D 1 R N0`
  for the seven plus rays at their registered floors.
- `oracle.jsonl` / `.exit`: `oracles/python/class_a_carrier_closure.py N0 --ray D,1,R`
  for the same seven rays; every count equals the Mojo count.
- `test_*.log` / `.exit`: the native tests `test_class_a_gap_theorem`,
  `test_class_a_gap_regime_descent`, `test_class_a_gap_uniform`, `test_gap_form`,
  `test_poly_hu`, `test_class_a_residue_rays` (the last over all 25 tabulated rays).
- `generator-regimes.log`, `generator-exceptional.log`, `descent-tables/*.json`:
  `oracles/python/class_a_descent_table.py` regenerating every regime descent
  table (`--ray d,eps,r --src ROWS --rows-fn F --tail-floor NLO`) from the sample
  ray's exports and every exceptional ray's rows and tables. The generator is
  not evidence.
- `graph-exports-sha256.txt`: digests of every exact graph export used
  (`class_a_residue_ray.mojo export D EPS N`): the sample rays of the 18
  regimes (`reg_*`, `l = 5..12`), the seven exceptional rays (`exc_*`,
  `l = 0..12`), and the `d = 2, 3, 4` exports from which the archived ray tables
  regenerate byte-identically (`g2m`, `g2p`, `g3m`, `g3p`, `g4p`, `g4m`; the
  `g4*` digests equal `evidence/class-a-d4-rays-2026-10-23/graph-exports-sha256.txt`).
  `graph-exports/` retains the minus `d=5` sample `n=25` and the plus `(5,1)`
  export at its floor `n=21`.
- `mojo-version.txt`, `manifest.json`: runtime, base commit, source digests,
  per-regime and per-ray counts, non-claims.

All logs are unedited combined stdout/stderr; `.exit` files are exit codes.
Local execution used the lock-matched compiler in `mojo-version.txt`; this is
not a CI receipt.

```sh
(cd kernel && pixi run --locked mojo run -I . class_a_gap_theorem.mojo certify-all 5)
(cd kernel && pixi run --locked mojo run -I . class_a_gap_uniform.mojo certify 1 0 1 5)
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_gap_theorem.mojo)
python oracles/python/class_a_carrier_closure.py 44 --ray 7,1,2
(cd evidence/class-a-gap-theorem-2026-10-23 && sha256sum -c SHA256SUMS)
```

`SHA256SUMS` covers every file in this packet except itself.
