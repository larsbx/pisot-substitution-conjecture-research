# Class-C plus-boundary descendant replay (2026-10-30)

Base: PR #405 merge 13e5ea48b02ecf9c0bce1e767b5f3b0aec586c88.
Canonical compiler: Mojo 1.1.0.dev2026090805 (34562fa1), matching pixi.lock.
Independent oracle: standard-library Python integer/Fraction literal words.

The proof in `docs/class-c-boundary-descendants-2026-10-30.md` classifies
two complete local stars for every d>=7 on plus c=0. This packet records
only their finite replay at every d=7..64: 116 stars, 638 distinct children
(summed per interface), 4,234 accepted occurrence pairs, 3,596 duplicates.
No closure or BH test is performed.

From kernel/:

    pixi run --locked mojo run -I . tests/test_class_c_boundary_descendants.mojo
    pixi run --locked mojo run -I . class_c_boundary_descendants.mojo dump > /tmp/class-c-boundary-descendants.txt

Then from repository root:

    python3 oracles/python/check_class_c_boundary_descendants.py --mojo-dump /tmp/class-c-boundary-descendants.txt --check-receipt evidence/class-c-boundary-descendants-2026-10-30/receipt.json

The deterministic full export's digest is recorded in receipt.json. CI
regenerates, checks and uploads it. Local receipt reproduction is not a
hosted CI result. Independent mathematical review remains pending.
