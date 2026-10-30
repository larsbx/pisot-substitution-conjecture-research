# Theorem T_C: class-C frozen tail, gaps d ≥ 6 (exact, symbolic)

Receipts for [`docs/class-c-tail-theorem-2026-10-28.md`](../../docs/class-c-tail-theorem-2026-10-28.md).
Everything is produced by the canonical Mojo driver
`kernel/class_c_tail_certificate.mojo` on the unchanged symbolic cone engine
`psc.symbolic_cone`.

| File | Command (from `kernel/`) | Content |
| --- | --- | --- |
| `theorem-plus.log` | `class_c_tail_certificate.mojo theorem 1` | cover of `d >= 6`, `n >= 4d`: one line per piece tried (certified or undecided) and per exact member, the summary line, then the common label set as typed rows |
| `theorem-minus.log` | `class_c_tail_certificate.mojo theorem -1` | the same for `n >= 4d + 4` |
| `native-test.log` | `tests/test_class_c_tail_certificate.mojo` | regression receipt: onset diagonals give the frozen sets, the `4d − 1` diagonal gives a different 198-label set, gap 6 from the onset refuses, a second label set refuses, malformed pieces refuse |
| `timings.txt` | `time` around the two theorem runs | wall-clock, local, both signs run concurrently |

The typed rows of both theorem logs equal, byte for byte, the rows of the
independent finite profile
`evidence/class-c-gap-profile-2026-10-28/frozen-tail-{plus,minus}.txt`
(650 members per sign, gaps 5..30). The workflow
`.github/workflows/class-c-tail-theorem.yml` replays both logs and the test
and diffs them against this packet.

## Replay

```
cd kernel
pixi run --locked mojo build -I . class_c_tail_certificate.mojo -o /tmp/cct
/tmp/cct theorem 1  | diff ../evidence/class-c-tail-theorem-2026-10-28/theorem-plus.log -
/tmp/cct theorem -1 | diff ../evidence/class-c-tail-theorem-2026-10-28/theorem-minus.log -
diff <(grep '^R ' ../evidence/class-c-gap-profile-2026-10-28/frozen-tail-plus.txt) \
     <(grep '^R ' ../evidence/class-c-tail-theorem-2026-10-28/theorem-plus.log)
diff <(grep '^R ' ../evidence/class-c-gap-profile-2026-10-28/frozen-tail-minus.txt) \
     <(grep '^R ' ../evidence/class-c-tail-theorem-2026-10-28/theorem-minus.log)
pixi run --locked mojo run -I . tests/test_class_c_tail_certificate.mojo
```

Local compiler: Mojo 1.1.0.dev2026090805 (34562fa1), the lock pin, from
Modular's nightly wheels in a virtual environment rather than via Pixi.
