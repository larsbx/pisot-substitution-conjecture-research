# Finite S18 outgoing completeness and quotient distances (2026-11-02)

Scope: the 22 named bounded specimens in `class_a_x_productivity.MEMBERS`.
Canonical Mojo checks literal outgoing completeness, exact S18 closure,
all-edge distance inequalities and actual lifted paths; an independent Python
Fraction oracle reconstructs both graphs and shortest distances.
No parameter-uniform X-carrier, nonunit realization bridge or PSC claim.

The implementation is in PR #447, based on original source
`4496dec08c8c1b064fd7c5894db9d67ffbdf373b`.
The subsequent receipt commit records its implementation source revision,
source SHA-256 manifest, exact commands/toolchain and execution outcomes.
Until those receipts are present, this directory is a replay contract and
must not be read as an acceptance receipt.

From `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_class_a_reversal_certificate.mojo --emit-certificates > /tmp/native-certificates.log
```

From root:

```sh
python -m pytest -q tests/test_class_a_x_productivity.py tests/test_class_a_x_transfer_plane.py tests/test_class_a_x_signed_strip.py tests/test_class_a_reversal_quotient.py tests/test_class_a_finite_certificates.py
python oracles/python/class_a_finite_certificates.py --native-log /tmp/native-certificates.log --certificates /tmp/certificates.json.gz
python oracles/python/class_a_finite_certificates.py --certificate /tmp/certificates.json.gz
```

The deterministic certificate contains every full original state, indexed
occurrence, orbit representative, both distances, selected quotient edge and
per-source Cartesian pair count. It can be replayed without the native log.
The dedicated workflow explicitly checks out the PR head revision and
archives all inputs/receipts; a queued or failed run is not acceptance.

Caps per specimen: 6,000 states and 20,000,000 nonterminal literal pairs.
All state and pair caps, checked-arithmetic failures and unresolved exact
signs refuse a verdict. Terminals are typed full-zero absorbing coincidences.

Mathematical derivation and scope boundary:
[contract](../../docs/class-a-reversal-native-2026-11-02.md).
Prior-art decision:
[stop/go](../../docs/class-a-completeness-distance-gate-2026-11-02.md).
