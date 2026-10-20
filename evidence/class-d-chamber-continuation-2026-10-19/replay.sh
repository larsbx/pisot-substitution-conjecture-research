#!/usr/bin/env bash
# From the repository root, after bootstrap-pinned-mojo.py has succeeded.
set -euo pipefail
: "${PSC_PINNED_MOJO_ROOT:?Set PSC_PINNED_MOJO_ROOT to the bootstrapped runtime}"
export MODULAR_MAX_PACKAGE_ROOT="$PSC_PINNED_MOJO_ROOT"
export MODULAR_MOJO_MAX_PACKAGE_ROOT="$PSC_PINNED_MOJO_ROOT"
export MODULAR_MOJO_MAX_IMPORT_PATH="$PSC_PINNED_MOJO_ROOT/lib/mojo"
mojo_bin="$PSC_PINNED_MOJO_ROOT/bin/mojo"
"$mojo_bin" --version
for test in test_overlap_child_sweep test_class_d_plus_positive_b_chambers test_class_d_chamber_sign test_symbolic_line_empty_blocks test_overlap_seed_patch; do
  "$mojo_bin" run -I kernel "kernel/tests/$test.mojo"
done
"$mojo_bin" build -I kernel kernel/class_d_plus_positive_b_chambers.mojo -o /tmp/psc-replay-plus-chambers
timeout 7200 stdbuf -oL -eL /tmp/psc-replay-plus-chambers
# Separate inherited regression gate; failure is not suppressed.
"$mojo_bin" run -I kernel kernel/tests/test_symbolic_line.mojo
