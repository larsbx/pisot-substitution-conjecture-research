# Plus-Class-A upper small members: local evidence

Date: November 20, 2026. Base source: `main@11c15bce` plus the change that adds
this packet. Written result and scope:
[`docs/class-a-plus-upper-small-members-2026-11-20.md`](../../docs/class-a-plus-upper-small-members-2026-11-20.md).

**Scope.** Complete swap-seed (S18) certificates for exactly the 70 members
`n=0..6, n+5<=d<=2n+11` of `x -> x y^(n+d) x, c -> c y^n x, y -> x y^(n+1) c`.
These are not all-strict-source statements. This packet holds **local**
receipts only; hosted exact-head acceptance is pending.

| File | Content |
| --- | --- |
| `native.log` | canonical Mojo run: one `CLASS_A_PLUS_SMALL_MEMBER_PASS n d states edges pairs depth path_edges` line per member, the total, and the contract receipt |
| `native.stderr` | empty |
| `mojo-version.txt` | `Mojo 1.1.0.dev2026090805 (34562fa1)`, from `kernel/pixi.lock` |
| `summary.json` | the independent oracle's per-member summaries (graph SHA-256, terminal labels, counts; certificates counted, not listed), totals, and the SHA-256 of the full emit transcript and of the full independent JSON |
| `pytest.log`, `pytest.xml` | `tests/test_class_a_plus_upper_small_certificate.py`, 195 cases |
| `environment.json` | toolchain and base revision |
| `source-inputs.sha256` | the exact inputs these receipts were produced from |
| `SHA256SUMS` | this directory |

The full emit transcript is 24 MB and the full independent JSON is 38 MB. They
are not committed because both are deterministic: regenerate them and compare
digests. Two emit runs gave the identical SHA-256
`4385f8f0a32ad4b595c68105c4185477ad42c1d15cfd4964a8f70b64c7a53fab`. The
`class-a-plus-constant-entry` workflow regenerates both on every relevant pull
request and uploads them as an artifact.

## Replay

```text
cd kernel
pixi run --locked mojo run -j 1 -I . tests/test_class_a_plus_upper_small_entry.mojo
pixi run --locked mojo run -j 1 -I . tests/test_class_a_plus_upper_small_entry.mojo --emit-certificates > /tmp/upper.log
sha256sum /tmp/upper.log
cd ..
python oracles/python/class_a_plus_small_certificate.py --native-log /tmp/upper.log --scope upper > /tmp/upper.json
python -m pytest -o addopts='' tests/test_class_a_plus_upper_small_certificate.py
sha256sum -c evidence/class-a-plus-upper-small-2026-11-20/source-inputs.sha256
```

A changed source refuses at the last step, and the receipts then describe the
recorded inputs only.
