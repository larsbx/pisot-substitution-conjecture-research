#!/usr/bin/env bash
# Download the pinned tla2tools.jar into tla/ and verify its digest.
# Idempotent: an existing jar is verified, not re-downloaded.
set -euo pipefail
cd "$(dirname "$0")"
PIN=tla2tools.pin
version=$(sed -n 's/^version=//p' "$PIN")
sha256=$(sed -n 's/^sha256=//p' "$PIN")
if [ -z "$version" ] || [ -z "$sha256" ]; then
    echo "$PIN does not pin both a version and a sha256" >&2
    exit 2
fi
if [ ! -f tla2tools.jar ]; then
    curl -fsSL -o tla2tools.jar \
        "https://github.com/tlaplus/tlaplus/releases/download/${version}/tla2tools.jar"
fi
if ! printf '%s  %s\n' "$sha256" tla2tools.jar | sha256sum -c - >/dev/null; then
    echo "tla/tla2tools.jar does not match the digest pinned in $PIN for ${version}." >&2
    echo "Delete it and re-run, or re-pin deliberately. Actual:" >&2
    sha256sum tla2tools.jar >&2
    exit 1
fi
echo "OK: tla2tools.jar matches the pinned ${version} digest."
