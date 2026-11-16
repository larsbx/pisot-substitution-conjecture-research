# Theorem CA run: boundary hitting on 𝒯_CA of the minus class-A chamber

Scope: the minus class-A chamber members `(k, t)` with `t <= 5` or
`t <= k - 1`, i.e. `𝒯_CA`. The derivation, hypotheses, transfer to the
oriented graph and non-claims are in
`docs/class-a-chamber-entry-stopgo-2026-11-15.md`. Status of Theorem CA:
repository-proved, computer-assisted, human review pending; not registered in
the claim ledger. The complement `{t >= 6, t >= k}` is not covered. Hosted
acceptance of `.github/workflows/class-a-chamber-entry.yml` is pending.

## Executed evidence

All runs used the final sources pinned in `source-digests.txt` (the drivers,
tests and their full PSC-side Mojo import closure, `kernel/pixi.toml` and
`kernel/pixi.lock`; the vendored packages are pinned by `vendored.toml`), with
Mojo 1.1.0.dev2026090805 (34562fa1) and pixi 0.81.0. Commands run from
`kernel/`.

* `native-cover.log`: `pixi run --locked mojo run -I . class_a_chamber_cone_certificate.mojo all`,
  36 min 3 s. Twelve families, 16 symbolic regions (largest 325 vertices), 116
  exact verdicts over 86 distinct members (largest 1,807 vertices), 0 non-PIP.
  Every symbolic and every exact vertex has an offset-zero descendant, and each
  region agrees with the exact graph at one cross-check point. Lines
  `... undecided: ...` are shifts at which the closure stopped on an undecided
  sign: no verdict, and the next shift was tried. A first run, before the
  bracket-order check was added to `certify_cone`, printed the same lines,
  timing aside.
* `native-coverage.log`: `... class_a_chamber_cone_certificate.mojo coverage`.
  The twelve families contain exactly the points of `𝒯_CA` in
  `0 <= k, t <= 200` (missed 0, stray 0), by exact membership solves. The
  all-parameter coverage proof is §6.1 of the note.
* `native-test-chamber-entry.log`: `tests/test_class_a_chamber_entry.mojo`, 7
  tests: the Bernstein rule (exact read, engine-level refusal of a dip at β,
  the sector sign), Lemma TW over `Q[k, t]`, the decomposition, the S9 transfer
  link at six members, and the line `t = 0` end to end.
* `native-test-symbolic-cone.log`: `tests/test_symbolic_cone.mojo`, the class-B
  regression, which passes with the rule off.
* `class-b-replay-plus.log`, `class-b-replay-minus.log`:
  `class_b_cone_certificate.mojo plus` and `minus` on the final sources, that is
  with the generic cover and the bracket-order check, compared with
  `archive/2026-10-08/class-b-cone-run/` (Theorem C).
  - plus: the certified-region lines are identical to the archive, as is the
    totals line `regions 32 finite 198 non-PIP 4 largest 297`.
  - minus: the certified-region lines and the exact-member lines are identical
    to the archive, as is the totals line
    `regions 45 finite 292 non-PIP 34 largest 274` (64 min 57 s).

Also run on the final sources and passing, logs not archived:
`tests/test_symbolic_line.mojo` (the capped-graph refusal added to
`exact_vertex_keys`), and the five class-C cone tests
(`test_class_c_lower_strip`, `test_class_c_below_three`,
`test_class_c_below_three_integration`, `test_class_c_tail_certificate`,
`test_class_c_strip_certificate`), which use the same engine with the rule off.

## Replay

```sh
cd kernel
pixi run --locked mojo run -I . class_a_chamber_cone_certificate.mojo coverage
pixi run --locked mojo run -I . class_a_chamber_cone_certificate.mojo all   # about 36 min
pixi run --locked mojo run -I . tests/test_class_a_chamber_entry.mojo
pixi run --locked mojo run -I . tests/test_symbolic_cone.mojo
pixi run --locked mojo run -I . class_b_cone_certificate.mojo plus           # Theorem C replay
pixi run --locked mojo run -I . class_b_cone_certificate.mojo minus
```

The hosted workflow `.github/workflows/class-a-chamber-entry.yml` runs the
first four.
