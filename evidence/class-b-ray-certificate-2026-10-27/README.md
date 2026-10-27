# Class-B top-layer residue-ray certificates (2026-10-27)

Unedited logs of local runs (not hosted CI) for
[docs/class-b-ray-certificate-2026-10-27.md](../../docs/class-b-ray-certificate-2026-10-27.md).
Each `*.exit` file holds the exit code of the run that wrote the matching
`*.log` (all 0).

| File | Command |
| --- | --- |
| `all.log` | `cd kernel && pixi run --locked mojo build -I . class_b_ray_certificate.mojo -o build/cbr && build/cbr all` |
| `native-test.log` | `cd kernel && pixi run --locked mojo run -I . -I tests tests/test_class_b_ray_certificate.mojo` |
| `oracle.log` | `python oracles/python/class_b_ray_certificate.py` |
| `pytest.log` | `python -m pytest -q tests/test_class_b_ray_certificate.py` |
| `tables-check.log` | `python oracles/python/class_b_ray_tables.py --check` |

`native.counts` and `oracle.counts` are the two count streams, one line per
ray, with the line tags removed (and the native `max_b` field dropped). They are
byte-identical:

```sh
diff native.counts oracle.counts
```

`all.log` contains, per ray:

- `CLASS_B_RAY_CERTIFICATE`: closure and descent for every `q >= q0`;
- two `CLASS_B_RAY_REPLAY` lines: native complete graph equal to the carrier
  and native descent of `X`, at the first two members;
- `CLASS_B_RAY_BELOW`: every PIP member of the residue class below `q0` is an
  exact uncapped graph that hits.

`inputs.sha256` records the sources these runs used (historical provenance, not
enforced on later edits). `SHA256SUMS` pins every
other file of this packet. The certificate is the Mojo one; the tables are a
generated proof target, and the Python verifier is an independent
cross-check. Compiler: Mojo from the locked `kernel/pixi.lock`.
