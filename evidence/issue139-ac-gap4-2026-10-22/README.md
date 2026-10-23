# Issue #139: class A/C gap-four evidence

Base: `ffd88e0716ee512b9444cce4c6789e7d0aa22306`. Scope and written
proof: `docs/issue139-ac-gap4-2026-10-22.md`. No universal gate is promoted.
Local execution date: 2026-10-23 UTC (continuation of the October 22 work).

## Canonical and independent receipts

- `native-a-tests.log`: all 18 registered A rays (10 existing, 8 new), full
  symbolic closure/descent, exact finite prefixes, two exact carrier/occurrence
  comparisons per ray, negative controls, and the A plus gap-four n=0 member.
- `native-c-tests.log`: both complete C gap-four certificates, every finite
  prefix member and two cross-checks per sign, domain and corrupted-pin controls.
- `native-typed-carrier-tests.log`: existing typed-carrier regression, including
  refusal outside the finite helper's newly explicit 4..32 budget.
- `c-plus-complete.log`, `c-minus-complete.log`: verbose native executions of
  the unchanged complete symbolic-line driver, including every prefix parameter.
- `ray-verdicts.json`: independent exact Fraction/Sturm closure and descent
  counts, least accepted floors for these fixed tables, and lower-floor refusals.
- `python-tests.log`: 42 existing/extended residue-ray and carrier tests;
  `python-negative-control.log`: 2 gap-four registry/candidate controls.
- `a-pre-refit-candidate.json` and `a-tail-descent-refusal.log`: a fitted rank
  that fails eventual descent despite using the same valid pieces and
  occurrences as the final certificate. The regression checks this refusal.
- `a-rank-countercontrol.json`: exact native n=36 edge `(32,37)` where the
  pre-refit rank is 17 at both endpoints, plus the full export hash.
- `a-short-fit-refusal.log`: earlier incomplete affine-piece synthesis.
- `c-plus-wedge-refusal.log`, `c-minus-wedge-refusal.log`: the complete C residual
  parameter covers refuse at a non-affine run-position bound. Both processes
  exited 1 within the stated 120-second budget; neither timed out.

A native A replay initially refused at the old n<=24 helper budget before
reaching the new n=28 cross-check. `a-initial-budget-refusal.txt` retains that
last receipt and the error; it is superseded by the completed replay, not
counted as mathematical failure or silently accepted.

## Runtime and reproducibility

Native executable version: `Mojo 1.1.0.dev2026090805 (34562fa1)`.
The compiler and Python runtime archives match `kernel/pixi.lock`:

```text
mojo-compiler-1.1.0.dev2026090805-release.conda
0d71889abb0887e2fa8a556c1081af4026034cdf98d27ad05b57cb096d7ad4f6
mojo-python-1.1.0.dev2026090805-release.conda
113c7d202236f943c91fdcb115f0a278e9c6027e1b7783bbc8b9a2076bb43838
```

Local execution extracted these archives into a minimal compiler/runtime,
setting `MODULAR_MAX_PACKAGE_ROOT`, `MODULAR_MOJO_MAX_PACKAGE_ROOT` and
`MODULAR_MOJO_MAX_IMPORT_PATH`. It was **not a complete Pixi installation**.
The optional crash reporter was absent; its compiler warning is not a proof
receipt. Run `bash evidence/issue139-ac-gap4-2026-10-22/replay.sh` for the full
locked-environment replay. The A residue-ray and dedicated C gap-four workflows
require fresh CI receipts; their status is separate from these local logs.
No full-repository Mojo, Lean, or TLA+ rerun is claimed for this scoped change.
The shared symbolic-line implementation and accepted class-D sources were
not edited. `source-digests.json` pins the local source inputs and the lock.

## Reconstruct the synthesis (optional; not proof evidence)

`graph-export-digests.json` records complete native export hashes and summaries
for both A signs, n=16..34. Full graph files are reproducible inputs, not
bundled here. From `kernel/`, build `class_a_residue_ray.mojo`; then export
with `build/ray export 4 EPS N > GRAPH_DIR/graph-nN.log`. Compare the hashes.
Only the ranges below enter the accepted candidates. Additional exploratory
exports outside this range carry no theorem claim and are not required.

First infer rows for all residues using n=16..27, then generate pieces and
occurrences with `--tail-floor 36`:

| eps | residues | fitting range | rank refit |
| --- | --- | --- | --- |
| +1 | 0,1 | 20..34 | r=0 only |
| +1 | 2,3 | 16..31 | none |
| -1 | 0,1,2 | 20..34 | all three |
| -1 | 3 | 16..31 | yes |

For example, from the repository root (use a disposable checkout because the
commands replace candidate table functions):

```bash
python oracles/python/class_a_descent_table.py GRAPH_DIR 16 --ray 4,1,0 --nhi 27 --rows-mojo kernel/psc/class_a_ray_d4p.mojo
python oracles/python/class_a_descent_table.py GRAPH_DIR 20 --ray 4,1,0 --nhi 34 --tail-floor 36 --mojo kernel/psc/class_a_ray_d4p.mojo
python oracles/python/class_a_ray_rank.py 4,1,0 36
python oracles/python/class_a_carrier_closure.py 24 --ray 4,1,0
```

Rank synthesis used NumPy 2.3.5 and SciPy 1.17.0. The floating optimizer only
proposes coefficients. Rational reconstruction, integer scaling and exact
oracle rejection precede writing; canonical exact Mojo verification is still
mandatory. A different optimizer may propose a different valid rank. The
committed integer tables, not reproducibility of an optimizer's choice,
are the proof object.

## Non-claims

Four entire infinite lines are covered, with explicit finite prefixes and
symbolic tails. No sampled graph plateau, finite fitting window, failed
spectral contraction argument or failed wedge checker proves family
exhaustion. A/C gaps d>=5, universal #139/#138/#84, G1 and PSC remain open.
Offset-zero hitting is an existential occurrence-compatible path statement,
not termination of all walks or equal-letter coincidence. Independent human
review remains pending.
