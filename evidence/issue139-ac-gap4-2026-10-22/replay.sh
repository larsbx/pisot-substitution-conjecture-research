#!/usr/bin/env bash
# From any directory. Full Pixi lock replay; local minimal-runtime receipt is
# separately labelled in README.md. Every mathematical decision is exact.
set -euo pipefail
cd "$(dirname "$0")/../.."
E=evidence/issue139-ac-gap4-2026-10-22
(cd "$E" && sha256sum -c SHA256SUMS)
python -m pytest -q tests/test_class_a_residue_rays.py tests/test_class_a_d2_plus_ray_carrier.py tests/test_issue139_gap_four.py
cd kernel
mkdir -p build/ac-gap-four
pixi run --locked mojo build -I . tests/test_class_a_residue_rays.mojo -o build/ac-gap-four/test-a
pixi run --locked mojo build -I . tests/test_class_c_gap_four.mojo -o build/ac-gap-four/test-c
build/ac-gap-four/test-a | tee build/ac-gap-four/native-a-tests.log
build/ac-gap-four/test-c | tee build/ac-gap-four/native-c-tests.log
diff ../"$E"/native-a-tests.log build/ac-gap-four/native-a-tests.log
diff ../"$E"/native-c-tests.log build/ac-gap-four/native-c-tests.log
