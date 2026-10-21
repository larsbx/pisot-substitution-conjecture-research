#!/usr/bin/env bash
# Run from the repository root. Full CI instead uses pixi install --locked.
set -euo pipefail
: "${PSC_PINNED_MOJO_ROOT:?Set to the hash-verified bootstrap destination from the previous packet}"
: "${TLA_TOOLS:?Set to tla2tools.jar; recorded archive hash is in tla-tool.sha256}"
export MODULAR_MAX_PACKAGE_ROOT="$PSC_PINNED_MOJO_ROOT"
export MODULAR_MOJO_MAX_PACKAGE_ROOT="$PSC_PINNED_MOJO_ROOT"
export MODULAR_MOJO_MAX_IMPORT_PATH="$PSC_PINNED_MOJO_ROOT/lib/mojo"
mojo_bin="$PSC_PINNED_MOJO_ROOT/bin/mojo"
"$mojo_bin" --version
"$mojo_bin" build -I kernel kernel/class_d_plus_positive_b_chambers.mojo -o /tmp/psc-aggregate-replay
# This command alone must emit the native whole-domain marker and return zero.
timeout 7200 stdbuf -oL -eL /tmp/psc-aggregate-replay
"$mojo_bin" run -I kernel kernel/tests/test_symbolic_line.mojo
python evidence/class-d-chamber-validation-2026-10-20/verify-manuscript-reconstruction.py
python tools/check_manuscript_source.py
bash tools/verify_all.sh provenance
PYTHONPATH=reference python -m pytest -q -o addopts='' tests/test_class_d_certificate_agreement.py tests/test_class_d_minus_certificate.py tests/test_line_certificate_workflow.py tests/test_ledger_generation.py tests/test_show_your_work_policy.py

bash proof/tla/check.sh
