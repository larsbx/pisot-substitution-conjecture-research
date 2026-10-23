# Fresh independent audit receipts

Scope: both class-A signs, d>=5, n>=5d. No n<5d, class-C, universal #139/#84,
G1 or PSC closure. No independent human review claimed.

Audited original: f1ce331bf051385acf8589d88088cbc2271d1350.
Core repair: 456275dc420d91d85c24b4579bda92bf0d5b050c (#340).
The false-sign regression and report accompany this packet.

Compiler: Mojo 1.1.0.dev2026090805 (34562fa1), matching kernel/pixi.lock.
The existing minimal installation requires a local MODULAR_HOME with paths
pointing to that installation. Normal locked Pixi provisioning failed on an
unreachable conda dependency. This is local native replay, not hosted acceptance.
Crashpad warnings in the logs do not change the recorded successful exits.

From kernel, each of the following completed with exit 0 using that compiler
and -I .:

- mojo run tests/test_gap_form.mojo -> gap_form-final.log
- mojo run tests/test_poly_hu.mojo -> poly_hu-final.log
- mojo run tests/test_class_a_gap_uniform.mojo -> closure.log
- mojo run tests/test_class_a_gap_regime_descent.mojo -> descent-final.log
- mojo run tests/test_class_a_gap_theorem.mojo -> theorem-test.log
- mojo run tests/test_overlap_zipper.mojo -> zipper.log
- mojo run tests/test_class_a_residue_rays.mojo -> residue-rays.log (all 25 rays)

Root commands, exit 0:

- python -m pytest -o addopts='' -q tests/test_class_a_residue_rays.py tests/test_class_a_d2_plus_ray_carrier.py tests/test_recorded_data_integrity.py -> python-final.log (115 passed)
- python oracles/python/class_a_gap_regime_adversarial.py -> adversarial-oracle.log
- PYTHONPATH=tools python -m claim_governance.cli --root . -> governance.log
- (cd evidence/class-a-gap-theorem-2026-10-23 && sha256sum -c SHA256SUMS) -> manifest.log

The six stress rays are exact all-l>=64 fixed-gap verifications, not a proof
uniform in the gap. The native assembly checks the universal certificates.

## Reproduce the original false sign

Create a temporary directory and write the original module with:

    git show f1ce331bf051385acf8589d88088cbc2271d1350:kernel/psc/poly_hu.mojo > TEMP/old_poly.mojo

From kernel, run:

    mojo run -I . -I TEMP ../evidence/class-a-gap-independent-audit-2026-10-23/false-sign-original.mojo

`false-sign-before.log` records ORIGINAL_CERTIFIED_SIGN 1 and
EXACT_POINT_SIGN -1. The original command exits 0: its wrong certificate is
the defect, not a failed process. `overflow-before.log` is the simpler
positive-coefficient/sign-corruption control. The corrected polynomial test
must refuse that sign-changing polynomial and checks the exact witness.

Hosted job: Class-A uniform gap theorem / exact-gap-theorem. Hosted acceptance
was queued when this packet was assembled and is not represented by these logs.
