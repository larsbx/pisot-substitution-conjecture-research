# Class-B step 2c exact evidence

Derivation, scope, hypotheses and remaining obligations:
[../../docs/class-b-middle-certificate-2026-10-27.md](../../docs/class-b-middle-certificate-2026-10-27.md).

- `labels/`: 546 native exact seed-graph exports, plus gaps 11–15 and minus
  gaps 8–11, `2g+8 <= q < 8g`.
- `carriers.json`: the 103 fitted new ray candidates, each with a certified
  floor raised by `2g`; all are independently certified symbolically.
- `core-labels/`: 150 native exact strict-core closures, five members on each
  of 15 middle rays per sign (`l=4..8`). These reproduce the 529-row tail from
  `l=5`; `l=4` is a containment calibration.
- `middle-candidates.json`, `middle-potentials.json`: finite exact synthesis
  inputs. The universal certificates, not synthesis or fits, prove anything
  about unbounded parameters.
- `verification/`: all 186 ray certificates, 372 actual graph replays and
  186 below-floor checks (576 PIP members), identical native/oracle count
  streams, uniform middle tests, independent rational checks and the Lean
  interface axiom audit.
- `negative-controls/`: preserved loose-hull source and refusal, rational
  non-member counterpoint, initial minus g=12 descent refusal, and actual
  strict children escaping the middle carrier outside its residue regime.
- `graph-benchmark.json`: generic/segmented labels match on both specimens;
  elapsed times were measured under concurrent load.
- `SOURCE_SHA256SUMS`: paths relative to the repository root, binding the
  canonical implementations, independent oracles, Lean interface, generators,
  verification workflow, and derivation. `SHA256SUMS` binds this packet's
  non-manifest files. Earlier packets are unchanged.

To regenerate the native exports into a **new** directory:

```bash
cd kernel
pixi run --locked mojo build -I . class_b_label_rays.mojo -o build/class-b-labels
pixi run --locked mojo build -I . class_b_core_exact.mojo -o build/class-b-core
cd ..
python oracles/python/class_b_step2c_exports.py --labels kernel/build/class-b-labels --core kernel/build/class-b-core --out /tmp/class-b-new-exports
```

To repeat all native ray certificates/replays and independent exact checks:

```bash
(cd kernel && pixi run --locked mojo build -I . class_b_ray_certificate.mojo -o build/class-b-rays)
python oracles/python/class_b_ray_replay.py --native kernel/build/class-b-rays --out /tmp/class-b-new-replay --offline-wrapper tools/run_without_network.py
```

Use the locked toolchain; local Mojo reports
`1.1.0.dev2026090805 (34562fa1)`. The standalone Lean interface was compiled
with `4.34.0-rc2` from source and checked for axioms; its five theorems use
only `propext`, `Classical.choice`, and `Quot.sound`. This receipt covers the
new interfaces, not a new full Lean verification of the chamber tables.

No universal BH, G1, A1′, #84, PSC, low/high residue or `l<4` conclusion is
claimed. No independent human review is represented as completed.
