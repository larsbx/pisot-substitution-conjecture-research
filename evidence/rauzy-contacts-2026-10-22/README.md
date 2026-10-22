# Exact Rauzy contacts — evidence bundle (2026-10-22)

Status: **exact**.
- The box verdict is the repository's own Theorem Ω verdict.
- Contacts rest on the cited Siegel–Thuswaldner boundary-graph criterion.
- Covering degree 1 is upstream's cited consequence of a productive box (Ito–Rao; Barge–Kwapisz). No record asserts it as a fact, and no ledger claim cites this bundle.

## Files

- `contacts-named.jsonl` — five named substitutions:
  - Tribonacci, flipped Tribonacci, Smith and #3742 (`122/201/12`), each with its verdict, every contact `[top, bottom, w0, w1, w2, x, y]`, its lattice neighbours and 8192 fractal points;
  - the non-unimodular control `011/20/0`, which is refused.
- `contacts-corpus.jsonl` — for each of the 4554 standing specimens: the verdict, the contact counts and the lattice neighbours. The 1926 non-unimodular specimens are refused.
- `summary.txt` — aggregates.

Kernel: `kernel/psc/rauzy_contacts.mojo`. Note: `docs/rauzy-contacts-stop-go-2026-10-22.md`.

## Replay

From the repository root:

```sh
cd kernel && pixi run rauzy-contacts-named  > ../evidence/rauzy-contacts-2026-10-22/contacts-named.jsonl
cd kernel && pixi run rauzy-contacts-corpus > ../evidence/rauzy-contacts-2026-10-22/contacts-corpus.jsonl  # ~5 min on 4 workers
python3 oracles/python/rauzy_contacts.py --check evidence/rauzy-contacts-2026-10-22/contacts-named.jsonl
python3 oracles/python/rauzy_contacts.py --check evidence/rauzy-contacts-2026-10-22/contacts-corpus.jsonl --limit 6
sha256sum -c evidence/rauzy-contacts-2026-10-22/SHA256SUMS
```

The oracle rebuilds the potential-overlap graph on a different region (`formal_overlap.FormalGraph`). It agrees on all five named records and on the first 6 corpus records (the pytest replay). The full corpus replay through the oracle takes hours and was not run.

## Sign and geometry checks (sampled, scratch scripts, not committed)

These used the exact 65,536-point sample of `rauzy-torus-2026-10-21`:

- **Tribonacci.** Every contact `R(i) + P(w)` comes within sampling distance of `R(j)`. With `−P(w)` instead, 14 pairs separate, which fixes the sign.
- **#3742.** All 148 contacts come within a sample gap of 0.016. The 40 nearest non-contact box vertices, by centroid, all stay at least 0.0845 apart.
