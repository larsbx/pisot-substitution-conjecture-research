# Hosted receipts for Theorem CA, Corollary CA-1 and Theorem C at `5ff3f9a5`

This packet holds the receipts on which three claims were registered:

- `MinusClassAChamberConeBoundaryHitting` (Theorem CA);
- `MinusClassAChamberConeEntry` (Corollary CA-1);
- `ClassBSectorBoundaryHitting` (Theorem C).

The mathematics, hypotheses and non-claims are in
`docs/class-a-chamber-entry-stopgo-2026-11-15.md` and
`docs/p1b-symbolic-cone-2026-10-08.md`. Status: computer-assisted, human
review pending. The earlier packet `evidence/class-a-chamber-cone-2026-11-15/`
is unchanged; it records the first runs, made before the bracket-order read
moved to a scratch region and before the capped-graph refusal was withdrawn.
Neither change alters any certified region, exact member or total.

## Hosted, exact head `5ff3f9a5cae45234884bea46779d7e4f9e3d851c` (merged as PR #585)

Workflow `.github/workflows/class-a-chamber-entry.yml`, pull-request run
43773184319, all four jobs `success`. Raw job logs:

| File | Job | Content |
| --- | --- | --- |
| `hosted-certificate-132993441031.log` | `certificate` | exact coverage of `t <= 5` or `t <= k - 1` up to 200, then all twelve families: `regions 16 finite 116 non-PIP 0 largest 325` |
| `hosted-regressions-132993441284.log` | `regressions` | `test_class_a_chamber_entry.mojo` 7/7 and `test_symbolic_cone.mojo` 9/9, with their contract receipts |
| `hosted-theorem-c-replay-plus-132993441198.log` | `theorem-c-replay (plus)` | `regions 32 finite 198 non-PIP 4 largest 297`; certified-region lines and totals diffed equal to `archive/2026-10-08/class-b-cone-run/plus.out` |
| `hosted-theorem-c-replay-minus-132993441219.log` | `theorem-c-replay (minus)` | `regions 45 finite 292 non-PIP 34 largest 274`; certified-region, exact-member and totals lines diffed equal to the archived `minus.out` |

## Local, the same sources

Mojo 1.1.0.dev2026090805, locked pixi environment; `source-digests-5ff3f9a5.txt`
pins the drivers, the engine, the tests and the pixi pins at that head.

- `local-coverage.log`: `class_a_chamber_cone_certificate.mojo coverage`, missed 0, stray 0.
- `local-test-chamber-entry.log`, `local-test-symbolic-cone.log`: 7/7 and 9/9.
- `local-class-b-replay-plus.log`: the plus cover. It is identical to the
  2026-11-15 replay, timing aside.

The local re-runs of the full class-A cover, the Theorem C minus cover and the
class-C below-three minus replay were interrupted by a container restart and
are not archived. The hosted `certificate` and `theorem-c-replay (minus)` jobs
above, and job `cover (minus)` 132993439959 of the `Class-C below-three cover`
run 43773184602 at the same head (`success`), ran them to completion.

## Replay

```sh
git checkout 5ff3f9a5cae45234884bea46779d7e4f9e3d851c
cd kernel
pixi run --locked mojo run -I . class_a_chamber_cone_certificate.mojo coverage
pixi run --locked mojo run -I . class_a_chamber_cone_certificate.mojo all
pixi run --locked mojo run -I . tests/test_class_a_chamber_entry.mojo
pixi run --locked mojo run -I . tests/test_symbolic_cone.mojo
pixi run --locked mojo run -I . class_b_cone_certificate.mojo plus
pixi run --locked mojo run -I . class_b_cone_certificate.mojo minus
```
