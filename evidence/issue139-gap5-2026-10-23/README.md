# Gap-five A/C exact evidence

Base main: `bbbf9017281c72493874c1d752e43cd1525873ef` (merged #326).
Scope and prior-art/hypothesis gate: `docs/issue139-gap5-2026-10-23.md`.

- `a-plus.log`, `a-minus.log`: complete seed graphs for the finite pilot only,
  plus n=0..12 and minus n=3..12. SUMMARY fields are n, vertices, maximum
  first-hit depth, recurrent vertices. The final marker denies a whole-line
  certificate and universal #139.
- `c-plus.log`, `c-minus.log`: complete symbolic-line runs, with progress for
  every expanded symbolic vertex, every finite-prefix parameter and both
  exact vertex-set cross-checks. A last-line certificate is earned only after
  all these obligations finish. Read the associated `.exit` as well.
- `domains.log`: native exact PIP/determinant/occurrence-label endpoint controls,
  invalid sign, preceding A-member refusal and a target-free-cycle control.
- `source-digests.json`: exact hashes of the local kernel and lock inputs.
- `validation.log`: local Python receipt/proof-bank/link/policy checks (70).
- `provenance-initial.log`: first audit refused the theorem opening without a
  nearby status label. The note was labelled explicitly; no mathematical or
  executable source changed. `provenance.log` is the successful rerun.
- Evidence integrity was checked separately after pinning and staging (53 tests).
- `replay.sh`: full locked Pixi replay and byte comparisons.

Local builds used the existing minimal lock-matched runtime
`Mojo 1.1.0.dev2026090805 (34562fa1)` with the compiler/Python archive hashes
recorded in `kernel/pixi.lock` and the gap-four packet. This is not a full
Pixi installation and is not a hosted CI receipt. The absent optional
crash reporter emitted a build warning; it is not a proof failure or receipt.
Set `MODULAR_MAX_PACKAGE_ROOT` and `MODULAR_MOJO_MAX_PACKAGE_ROOT` to that
runtime root and `MODULAR_MOJO_MAX_IMPORT_PATH` to its `lib/mojo`. Build with:

```bash
"$MODULAR_MAX_PACKAGE_ROOT/bin/mojo" build -I kernel kernel/class_c_gap_five.mojo -o /tmp/gap-five-c
"$MODULAR_MAX_PACKAGE_ROOT/bin/mojo" build -I kernel kernel/class_a_gap_five_probe.mojo -o /tmp/gap-five-a
"$MODULAR_MAX_PACKAGE_ROOT/bin/mojo" build -I kernel kernel/tests/test_gap_five_domains.mojo -o /tmp/gap-five-domains
```

Each C sign had a 1200-second wall budget; each A pilot a 300-second budget.
C signs were run concurrently; neither uses randomness. Exit 124 would mean
budget exhaustion, never a non-hitting counterexample or a certificate.

The new dedicated workflow rebuilds with full locked Pixi and replays each
sign independently, including receipt comparisons and artifact retention.
Hosted acceptance is recorded separately; it is not inferred from local logs.
No full repository Mojo/Lean/TLA+ replay is claimed. Historical gap-four
packets and accepted class-D results are unchanged. Whole-line class-A gap
five, all larger gaps, universal boundary hitting, G1 and PSC remain open.
Independent human mathematical review remains pending.

## Correction, 2026-10-30

`c-plus.log` and `c-minus.log` were regenerated after the fit-first change
to `kernel/psc/symbolic_line.mojo`. Only the `sign_reads=` field of the final
line changes (6858 → 5820, 7658 → 6276). `source-digests.json` and the
`*.exit` files record the original run and are unchanged.
