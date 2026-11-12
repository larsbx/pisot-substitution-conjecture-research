#!/usr/bin/env bash
# Run in the pinned Lake environment after building PscVerif.NamedArchivedGraph.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
if [[ $# != 2 ]]; then
    echo "usage: $0 NATIVE_PACKET OUTPUT_DIRECTORY" >&2
    exit 2
fi
python3 "$root/tools/import_archived_c4.py" "$1" "$2"
cp "$root"/proof/ArchivedC4/*.lean "$2"
cd "$2"
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"

compile() {
    echo "Checking $1"
    lean -o "$1.olean" "$1.lean"
}
compile Check
compile Contraction
compile Geometry
for fixture in 0 1; do
    for source in Fixture"${fixture}"Leaves*.lean; do
        compile "${source%.lean}"
    done
    compile "Fixture${fixture}Data"
    for source in Fixture"${fixture}"Rows*.lean Fixture"${fixture}"Controls.lean; do
        compile "${source%.lean}"
    done
    compile "Fixture${fixture}Accepted"
    compile "Fixture${fixture}Bridge"
done
