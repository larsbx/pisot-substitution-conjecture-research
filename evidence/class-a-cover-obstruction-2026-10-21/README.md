# Class-A rectangular cover obstruction

The written uniform argument is `docs/class-a-cover-obstruction-2026-10-21.md`.
The canonical Mojo regression checks symbolic identities, real ordered edges
at n=4,8,18,64,256, and negative controls. Its complete seed graphs at n=4,18
omit both witnesses. The independent Fraction oracle agrees at those two
members. This is not uniform seed exclusion and not a failure of BH.

`native-tests.log` and `driver.log` are unedited combined stdout/stderr;
corresponding `.exit` files are process exit codes. `oracle.json`,
`oracle.stderr`, and `oracle.exit` preserve the separate oracle result.
The Crashpad initialization warning did not prevent native execution.
`manifest.json` pins new sources and the reused lock-matched minimal runtime.
`kernel-source-sha256.json` pins every current kernel source/manifest/lock;
new source snapshots are also retained. No fresh full-Pixi or CI receipt is
claimed here. The dedicated workflow produces its own fresh locked receipts.

Replay from the repository root:

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_class_a_cover_obstruction.mojo)
(cd kernel && pixi run --locked mojo run -I . class_a_cover_obstruction.mojo 18)
python oracles/python/class_a_cover_obstruction.py
```

`SHA256SUMS` covers every file in this packet except itself. No accepted
class-D certificate or receipt is modified.
