# Theorem T_C2: class C on the band 3d ≤ n below the onset

Receipts for [`docs/class-c-strip-theorem-2026-10-29.md`](../../docs/class-c-strip-theorem-2026-10-29.md),
produced by the canonical driver `kernel/class_c_tail_certificate.mojo` on
the unchanged engine `psc.symbolic_cone`.

| File | Command (from `kernel/`) | Content |
| --- | --- | --- |
| `strip-plus.log` | `class_c_tail_certificate.mojo strip 1` | Cover of `3d ≤ n < 4d`, every gap: one line per piece tried (certified or undecided) and per exact member, a summary line, then every distinct label set as typed rows (25 sets) |
| `strip-minus.log` | `class_c_tail_certificate.mojo strip -1` | The same for `3d ≤ n < 4d + 4` (49 sets) |
| `native-test.log` | `tests/test_class_c_strip_certificate.mojo` | Regression receipt: the strip diagonal `j = 5` and the line `n = 3d` against exact graphs, the several-set cover, refusals of malformed strip pieces |
| `timings.txt` | `time` around the two runs | Wall-clock time, local, both signs concurrently |

## Replay

```
cd kernel
pixi run --locked mojo build -I . class_c_tail_certificate.mojo -o /tmp/cct
/tmp/cct strip 1  | diff ../evidence/class-c-strip-theorem-2026-10-29/strip-plus.log -
/tmp/cct strip -1 | diff ../evidence/class-c-strip-theorem-2026-10-29/strip-minus.log -
pixi run --locked mojo run -I . tests/test_class_c_strip_certificate.mojo
```

Adding the `STRIP` frame left T_C unchanged. After the change,
`theorem 1`, `theorem -1` and `tests/test_class_c_tail_certificate.mojo`
reproduce `evidence/class-c-tail-theorem-2026-10-28/` byte for byte.

Local compiler: Mojo 1.1.0.dev2026090805 (the lock pin), from Modular's
nightly wheels.
