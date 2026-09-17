#!/usr/bin/env bash
# Run every Mojo regression test under tests/.
#
# One loop over tests/test_*.mojo, so a new test file is picked up by adding
# the file -- there is no chain of names to keep in step, and a forgotten entry
# cannot silently drop coverage. Every test runs even after a failure, so one
# run reports every broken contract, and the exit status is nonzero if any
# failed.
set -uo pipefail
cd "$(dirname "$0")"

status=0
ran=0
failed=()
for test in tests/test_*.mojo; do
    ran=$((ran + 1))
    if ! mojo run -I . "$test"; then
        status=1
        failed+=("$test")
    fi
done

printf '\n%d Mojo test files run.\n' "$ran"
if (( status == 0 )); then
    printf 'All passed.\n'
else
    printf 'FAILED: %s\n' "${failed[*]}"
fi
exit "$status"
