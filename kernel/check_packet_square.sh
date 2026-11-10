#!/usr/bin/env bash
# Regenerate the packet-square-v1 evidence and the Lean data modules, compare
# bytes, and check the CLI refusals. No math here: every row is computed and
# verified by kernel/psc/packet_square_export.mojo, and the Lean emitter is
# checked row by row against the committed JSONL by
# kernel/tests/test_packet_square_export.mojo, which this script runs.
#
# Usage: pixi run bash check_packet_square.sh [--no-lean-compare]
#
# Default mode: every committed Lean data module must exist and equal the
# regenerated module byte for byte. A missing module is an ERROR (exit 1).
# PASS is printed only in this mode, and only after every check.
#
# --no-lean-compare: for use before the data modules are committed. Every
# other check runs, and the Lean modules are regenerated, but they are not
# compared with committed files. The script then prints INCOMPLETE and exits
# 2. It never prints PASS: an uncompared surface is not a passed one.
#
# Every gate here is in the refuse-to-proceed column of the AGENTS.md
# fail-closed table (a cap is not a verdict; a generated surface that
# disagrees with its table refuses the run). None deletes or overwrites a
# committed file: the regenerated files go to kernel/build only.
#
# The committed modules are named by one variable, lean_prefix: module =
# lean_prefix + fixture suffix, file = ../proof/PscVerif/<module, dots as
# slashes>.lean. "PscVerif.PacketSquareData." names
# PscVerif/PacketSquareData/Tribonacci.lean; the flat layout of the design
# brief (section 8.1, row K) is "PscVerif.PacketSquareData", which names
# PscVerif/PacketSquareDataTribonacci.lean. Set it at integration to the layout
# that is committed.
#
# This check reads more than its own files. The driver takes parse_sigma and
# parse_positive from the archived driver kernel/target_aware_bpa.mojo, and
# the module takes ints_json from kernel/psc/target_packet_report.mojo. Its
# psc import closure is target_packets, target_packet_report,
# packet_hub_analysis, bpa, bounded_bpa, pisot, words, affine_ancestry_trace,
# bd_endpoint, derived_system, endpoint_core, exact, hierarchy_offset,
# hub_selector, legal_tower, renewal and renewal_address, plus the vendored
# finite_exact, finite_graph, finite_linear_algebra, mojo_smoke and
# substitution_dynamics. A workflow path filter for this check must cover all
# of them (kernel/psc/**, the vendored package directories,
# kernel/target_aware_bpa.mojo, kernel/pixi.*), the four files of this
# package, evidence/packet-square-2026-11-10/** and the committed Lean data
# modules.
set -euo pipefail
cd "$(dirname "$0")"

compare_lean=1
if [ "$#" -gt 1 ]; then
    echo "usage: check_packet_square.sh [--no-lean-compare]" >&2
    exit 1
fi
if [ "$#" -eq 1 ]; then
    if [ "$1" = "--no-lean-compare" ]; then
        compare_lean=0
    else
        echo "usage: check_packet_square.sh [--no-lean-compare]" >&2
        exit 1
    fi
fi

lean_prefix="PscVerif.PacketSquareData."
lean_root=../proof/PscVerif

mkdir -p build
mojo build -I . packet_square_export.mojo -o build/packet-square-export
driver=build/packet-square-export
fixtures=../evidence/packet-square-2026-11-10
for fixture in tribonacci real-secondary non-pisot-strict gf-actual; do
    case "$fixture" in
        tribonacci) key=01/02/0; suffix=Tribonacci ;;
        real-secondary) key=1/02/202; suffix=RealSecondary ;;
        non-pisot-strict) key=1/012/1; suffix=NonPisot ;;
        gf-actual) key=1/2/021; suffix=GfActual ;;
    esac
    "$driver" --sigma "$key" --target any --hub-rows > "build/packet-square-$fixture.jsonl"
    cmp "$fixtures/$fixture.jsonl" "build/packet-square-$fixture.jsonl"
    module="$lean_prefix$suffix"
    "$driver" --sigma "$key" --target any --format lean --module "$module" --hub-rows \
        > "build/packet-square-$suffix.lean"
    committed="$lean_root/${module//.//}.lean"
    if [ "$compare_lean" -eq 1 ]; then
        if [ ! -f "$committed" ]; then
            echo "ERROR: committed Lean data module $committed is missing (module $module)" >&2
            exit 1
        fi
        cmp "$committed" "build/packet-square-$suffix.lean"
    else
        echo "NOT COMPARED: $committed (module $module), --no-lean-compare"
    fi
done
(cd "$fixtures" && sha256sum -c SHA256SUMS)

# The Lean emitter, row by row against the committed JSONL, and the mutation
# controls: the regression test of this package.
mojo run -I . -I tests tests/test_packet_square_export.mojo > build/packet-square-test.log 2>&1 || {
    cat build/packet-square-test.log >&2
    echo "ERROR: tests/test_packet_square_export.mojo failed" >&2
    exit 1
}
grep -q '^contract-receipt: packet-square-v1 export: ' build/packet-square-test.log

# Every budget refuses: exit nonzero, stdout is exactly the budget row with
# the given cap (and, for the automaton budgets, the inconclusive row naming
# the exhausted budget), and stderr names the refusal. In Lean mode nothing
# reaches stdout.
for budget in state length packet edge; do
    states=20000; length=10000; packets=200000; edges=2000000; tail=""
    case "$budget" in
        state) states=1; tail='{"record":"inconclusive","budget_kind":1}'
               refusal='BPA budget exhausted; no packet-square table' ;;
        length) length=1; tail='{"record":"inconclusive","budget_kind":2}'
                refusal='BPA budget exhausted; no packet-square table' ;;
        packet) packets=1; refusal='packet cap exhausted: diagnostic inconclusive' ;;
        edge) edges=1; refusal='packet edge cap exhausted: diagnostic inconclusive' ;;
    esac
    out="build/packet-square-$budget-cap.out"
    err="build/packet-square-$budget-cap.err"
    if "$driver" --sigma 1/02/202 "--$budget-cap" 1 > "$out" 2> "$err"; then
        echo "ERROR: exhausted $budget cap succeeded" >&2
        exit 1
    fi
    printf '{"record":"budget","bpa_states":%s,"bpa_length":%s,"packets":%s,"edges":%s}\n' \
        "$states" "$length" "$packets" "$edges" > "build/packet-square-$budget-cap.expected"
    if [ -n "$tail" ]; then
        printf '%s\n' "$tail" >> "build/packet-square-$budget-cap.expected"
    fi
    if ! cmp -s "build/packet-square-$budget-cap.expected" "$out"; then
        echo "ERROR: exhausted $budget cap printed other than its budget row (and inconclusive row):" >&2
        cat "$out" >&2
        exit 1
    fi
    if ! grep -qF "$refusal" "$err"; then
        echo "ERROR: exhausted $budget cap did not refuse with: $refusal" >&2
        cat "$err" >&2
        exit 1
    fi
    if "$driver" --sigma 1/02/202 "--$budget-cap" 1 --format lean --module Scratch.Capped \
            > "build/packet-square-$budget-cap-lean.out" 2> "build/packet-square-$budget-cap-lean.err"; then
        echo "ERROR: exhausted $budget cap emitted a Lean module" >&2
        exit 1
    fi
    if [ -s "build/packet-square-$budget-cap-lean.out" ]; then
        echo "ERROR: exhausted $budget cap printed Lean text" >&2
        exit 1
    fi
    if ! grep -qF "$refusal" "build/packet-square-$budget-cap-lean.err"; then
        echo "ERROR: exhausted $budget cap (Lean) did not refuse with: $refusal" >&2
        exit 1
    fi
done

# Synchronize mode is outside the schema.
if "$driver" --sigma 1/02/202 --target sync-right > build/packet-square-sync.out 2> build/packet-square-sync.err; then
    echo "ERROR: sync-right succeeded" >&2
    exit 1
fi
grep -qF 'synchronize_right is outside packet-square-v1' build/packet-square-sync.err
if [ -s build/packet-square-sync.out ]; then
    echo "ERROR: sync-right printed rows" >&2
    exit 1
fi

# Malformed inputs refuse, with their own message, before any row is printed.
invalid=(
    "--sigma x/1/2|sigma images must contain only digits 0..2"
    "--sigma|missing value for packet-square option"
    "--target 3|target must be any, 0, 1 or 2"
    "--format csv|format must be jsonl or lean"
    "--format lean|--format lean needs --module"
    "--module A.B|--module applies only to --format lean"
    "--format lean --module 1bad|Lean module component must start with a letter or _"
    "--state-cap 0|diagnostic budget must be positive"
    "--packet-cap x|diagnostic budget must be a positive integer"
    "--frobnicate 1|unknown packet-square option"
)
for entry in "${invalid[@]}"; do
    args="${entry%%|*}"
    want="${entry#*|}"
    # shellcheck disable=SC2086
    if "$driver" $args > build/packet-square-invalid.out 2> build/packet-square-invalid.err; then
        echo "ERROR: invalid arguments succeeded: $args" >&2
        exit 1
    fi
    if [ -s build/packet-square-invalid.out ]; then
        echo "ERROR: invalid arguments printed rows: $args" >&2
        exit 1
    fi
    if ! grep -qF -e "$want" build/packet-square-invalid.err; then
        echo "ERROR: invalid arguments $args did not refuse with: $want" >&2
        cat build/packet-square-invalid.err >&2
        exit 1
    fi
done

if [ "$compare_lean" -eq 1 ]; then
    echo "PASS packet-square-v1: JSONL reproduction, committed Lean data modules byte for byte ($lean_prefix*), Lean emission row by row against the JSONL, checksums, fail-closed caps, sync-right and malformed input"
    exit 0
fi
echo "INCOMPLETE packet-square-v1: committed Lean data modules not compared (--no-lean-compare); every other check passed"
exit 2
