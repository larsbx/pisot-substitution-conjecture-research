# Finite S18 outgoing completeness and quotient distances (2026-11-02)

Scope: the 22 named bounded specimens in `class_a_x_productivity.MEMBERS`.
Canonical Mojo checks literal outgoing completeness, exact S18 closure,
all-edge distance inequalities and actual lifted paths; an independent Python
Fraction oracle reconstructs both graphs and shortest distances.
No parameter-uniform X-carrier, nonunit realization bridge or PSC claim.

The implementation is in PR #447, based on original source
`4496dec08c8c1b064fd7c5894db9d67ffbdf373b`.
**Executed implementation revision:** `f7d4731e3be97e592b921af9681bf5f137f16475`,
source tree `9212dd1be4a5e8970c7ebbc7d3e3488bda31e361`.
Local exact-source native execution, 41 Python tests, full independent
literal/Fraction replay, archived-certificate replay, source manifest and
provenance checks **all passed**. Native stderr is empty. Two native runs and
two certificate generations were byte-for-byte identical.

Totals: 16,132 original states, 8,088 quotient orbits, 190,966 indexed edges,
3,224,980 distinct scanned source/address pairs and 60,330 selected path steps.
The native regression includes 16 refusal controls. Maximal shortest terminal
distance is 12, attained in (0,8). These counts sum the specimens, not a uniform
carrier. The checker may scan the same pairs in separate verification passes.

`receipt.json` identifies commands, caps, exact source and outcomes;
`source-inputs.sha256` pins replay inputs at that revision; `source-tree.txt`
pins the whole source tree. `native-certificates.log.gz` is the actual native
stdout. `certificates.json.gz` is canonical JSON with deterministic gzip
mtime=0; `verification.json` and `certificate-replay.json` independently
validate its records. SHA256SUMS pins every file in this packet. Source paths
are checked from repository root **at the recorded implementation revision**.
Later evidence-only commits do not change the replay implementation.

Hosted exact-head acceptance was still queued when this receipt was recorded:
[run 41447675233](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41447675233).
This local receipt is not a hosted pass or independent human review. PR #447
stays draft pending the hosted gate. No governed claim is promoted.

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

## Replaying the archived files

From the repository root at the recorded source revision (copy or extract the
packet from the evidence commit when checking out the implementation commit):

```sh
sha256sum -c evidence/class-a-finite-certificates-2026-11-02/source-inputs.sha256
gzip -dc evidence/class-a-finite-certificates-2026-11-02/native-certificates.log.gz > /tmp/native-certificates.log
python oracles/python/class_a_finite_certificates.py --native-log /tmp/native-certificates.log --certificates /tmp/certificates.json.gz
python oracles/python/class_a_finite_certificates.py --certificate evidence/class-a-finite-certificates-2026-11-02/certificates.json.gz
```

## Per-specimen independently checked results

| k | t | Original | Orbits | Indexed edges | Literal pairs | Maximum distance |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 0 | 784 | 393 | 4788 | 34778 | 7 |
| 0 | 1 | 1010 | 506 | 7752 | 71696 | 8 |
| 0 | 2 | 1220 | 611 | 11226 | 124730 | 8 |
| 0 | 3 | 1440 | 721 | 15098 | 198668 | 8 |
| 1 | 0 | 436 | 219 | 3142 | 27300 | 4 |
| 1 | 1 | 642 | 322 | 5636 | 60544 | 6 |
| 1 | 2 | 646 | 324 | 6678 | 83712 | 5 |
| 1 | 3 | 836 | 419 | 9574 | 140920 | 5 |
| 2 | 0 | 378 | 190 | 3144 | 32768 | 5 |
| 2 | 1 | 390 | 196 | 3794 | 46360 | 4 |
| 2 | 2 | 594 | 298 | 6656 | 94950 | 5 |
| 2 | 3 | 568 | 285 | 7092 | 116176 | 4 |
| 3 | 0 | 352 | 177 | 3252 | 38518 | 4 |
| 3 | 1 | 342 | 172 | 3670 | 51088 | 4 |
| 3 | 2 | 362 | 182 | 4432 | 69040 | 4 |
| 3 | 3 | 548 | 275 | 7464 | 132286 | 4 |
| 0 | 4 | 1632 | 817 | 19350 | 291318 | 8 |
| 4 | 0 | 340 | 171 | 3526 | 47270 | 4 |
| 4 | 4 | 518 | 260 | 8252 | 173834 | 4 |
| 0 | 8 | 2312 | 1157 | 40118 | 902194 | 12 |
| 8 | 0 | 326 | 164 | 4816 | 94262 | 4 |
| 8 | 8 | 456 | 229 | 11506 | 392568 | 4 |
