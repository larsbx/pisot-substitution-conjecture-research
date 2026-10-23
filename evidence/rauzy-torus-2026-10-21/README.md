# Rauzy fractals on the 2-torus — evidence bundle (2026-10-21)

Status: **diagnostic**. Nothing here is a certificate, and no ledger claim or status surface may cite it.

## Files

- `named.jsonl` — one `psc-rauzy-torus/v1` record per named substitution: Tribonacci, flipped Tribonacci, Smith, and the non-unimodular control `011/20/0`, which is refused. Each record carries:
  - 8192 fractal points and their subtile letters;
  - the lift profile on a 64 × 64 grid.
- `corpus.jsonl` — one summary record for each of the 4554 standing PIP specimens: 4096 points and a 32 × 32 grid each. The 1926 non-unimodular specimens are refused.
- `summary.txt` — aggregates of both files.

## Semantics

Kernel: `kernel/psc/rauzy_torus.mojo`; note: `docs/rauzy-torus-stop-go-2026-10-21.md`.

- `freq_floor[i]` is the certified `⌊2⁴⁰ f_i⌋`.
- `x`, `y` are `⌊2¹⁶ · hi_i / 2⁴⁰⌋`, where `2⁴⁰ D_ni ∈ [hi_i − n, hi_i]`.
- `lifts[cx·G + cy]` counts the distinct `Z²`-lifts that the sample meets in torus cell `(cx, cy)`.
- `undecided` counts the points whose enclosure straddles a grid line. They are never assigned to a cell.

## Replay

From the repository root:

```sh
cd kernel && pixi run rauzy-torus-named > ../evidence/rauzy-torus-2026-10-21/named.jsonl
cd kernel && pixi run rauzy-torus-corpus > ../evidence/rauzy-torus-2026-10-21/corpus.jsonl   # about 6 min
python3 oracles/python/rauzy_torus.py --check evidence/rauzy-torus-2026-10-21/named.jsonl
python3 oracles/python/rauzy_torus.py --check evidence/rauzy-torus-2026-10-21/corpus.jsonl   # independent exact oracle: 0 mismatches
sha256sum -c evidence/rauzy-torus-2026-10-21/SHA256SUMS
```

## Finite observation, and the limit of the estimator

Specimen #3742 (`122/201/12`, unimodular-complex) has the lowest one-lift share, `44/1024`. A follow-up run varied the sample: points `n ∈ {4096, 16384, 65536}` and grids `G ∈ {8, 16, 32}`. Every cell had **at least two lifts** at `n ≥ 16384`, and the sup discrepancy was about `1.66`. Tribonacci, at the same settings, keeps a 0.9–0.97 one-lift share.

Adding points only discovers more lifts, never fewer. Refining the grid is bounded by point density. So a fractal with thin features cannot show its single-lift interior at any resolution this sampler reaches.

This is **not** evidence that #3742 has covering degree ≥ 2. Settling that question exactly is the job of the balanced-pair and overlap-coincidence kernels, not of this picture.
