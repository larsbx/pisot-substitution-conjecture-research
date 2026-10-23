#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
E=evidence/class-a-gap-sign-2026-10-23
(cd "$E" && sha256sum -c SHA256SUMS)
mkdir -p kernel/build/gap-sign
(cd kernel && pixi run --locked mojo build -I . tests/test_class_a_gap_sign.mojo -o build/gap-sign/test)
kernel/build/gap-sign/test > kernel/build/gap-sign/native.log
diff "$E/native.log" kernel/build/gap-sign/native.log
python oracles/python/class_a_gap_sign.py kernel/build/gap-sign/native.log > kernel/build/gap-sign/oracle.log
diff "$E/oracle.log" kernel/build/gap-sign/oracle.log
python -m pytest -q tests/test_class_a_gap_sign.py
