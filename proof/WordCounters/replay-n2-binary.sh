#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
    echo "usage: $0 recorded-elf" >&2
    exit 2
fi

root=$(git rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -- "$1" "$work/recorded"

check_identity() {
    local digest=8698153ffc6436ee155c15e8535634303bdafeee870a03f77c03bdeba6f2a204
    printf '%s  %s\n' "$digest" "$1" | sha256sum --check --status
}

if ! check_identity "$work/recorded"; then
    echo "recorded N2 ELF SHA-256 mismatch" >&2
    exit 1
fi

cd "$root"
slice=proof/WordCounters/N2MachineSlice.lean
lean --run "$slice" "$work/recorded"
while read -r name offset; do
    python3 - "$work/recorded" "$work/$name" "$offset" <<'PY'
from pathlib import Path
import sys

source, output, offset = sys.argv[1:]
data = bytearray(Path(source).read_bytes())
data[int(offset, 16)] ^= 1
Path(output).write_bytes(data)
PY
    if check_identity "$work/$name"; then
        echo "identity accepted mutation $name" >&2
        exit 1
    fi
    if lean --run "$slice" "$work/$name" >"$work/rejection.log" 2>&1 ||
        ! grep -Fq 'counter instruction bytes differ' "$work/rejection.log"; then
        cat "$work/rejection.log" >&2
        echo "slice checker did not reject $name with the expected diagnostic" >&2
        exit 1
    fi
    echo "Rejected $name"
done <<'CONTROLS'
guard-instruction aa96
overflow-branch aac7
stack-spill ab0e
first-cleanup-branch accb
second-cleanup-branch acf5
cleanup-call acfd
return-instruction ad4d
message-byte d5b0
CONTROLS

# The snapshot checked above is the one executed here.
chmod u+x "$work/recorded"
"$work/recorded"
