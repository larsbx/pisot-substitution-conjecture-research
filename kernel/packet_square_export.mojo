"""Packet-square exporter (schema packet-square-v1). Run with --help for inputs, budgets and formats.

Builds the complete balanced-pair automaton under a state and a length budget,
the target-aware packet graph under a packet and an edge budget, and exports
it as JSONL (`--format jsonl`, default) or as a Lean data module of
`Psc.PacketCertificate.Table (Fin 3)` (`--format lean --module NAME`). Every
row is verified by `verify_packet_square` before the first row after the
budget row is printed. A budget that runs out exits nonzero: in JSONL the
budget row (and, for the automaton budgets, an `inconclusive` row) is all
that is printed; in Lean nothing is printed. `--target sync-right` refuses:
stop-at-success at a noncoincident state is outside packet-square-v1.
The output is finite certificate input for the Lean checker, not a verdict;
it moves no claim and says nothing about C4, G1 or PSC.
"""

from std.sys import argv
from psc.bounded_bpa import build_bounded
from psc.bpa import sigma3
from target_aware_bpa import parse_sigma, parse_positive
from psc.packet_square_export import (
    build_packet_square, emit_packet_square_jsonl, emit_packet_square_lean,
    parse_packet_square_target, check_lean_module_name, budget_json, sigma_text,
)


def main() raises:
    var args = argv()
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var state_cap = 20000
    var length_cap = 10000
    var packet_cap = 200000
    var edge_cap = 2000000
    var target = -1
    var target_text = String("any")
    var format = String("jsonl")
    var module = String("")
    var hub_rows = False
    var i = 1
    while i < len(args):
        var option = args[i]
        if option == "--help":
            print("packet_square_export.mojo [--sigma 1/02/202] [--target any|0|1|2]")
            print("[--state-cap N] [--length-cap N] [--packet-cap N] [--edge-cap N]")
            print("[--format jsonl|lean] [--module Lean.Module.Name] [--hub-rows]")
            print("packet-square-v1; zero-based letters; caps and sync-right refuse; never a theorem verdict.")
            return
        if option == "--hub-rows":
            hub_rows = True
        else:
            if i + 1 >= len(args):
                raise Error("missing value for packet-square option")
            i += 1
            var value = args[i]
            if option == "--sigma":
                sigma = parse_sigma(value)
            elif option == "--state-cap":
                state_cap = parse_positive(value)
            elif option == "--length-cap":
                length_cap = parse_positive(value)
            elif option == "--packet-cap":
                packet_cap = parse_positive(value)
            elif option == "--edge-cap":
                edge_cap = parse_positive(value)
            elif option == "--target":
                target = parse_packet_square_target(value)
                target_text = String(value)
            elif option == "--format":
                if value != "jsonl" and value != "lean":
                    raise Error("format must be jsonl or lean")
                format = String(value)
            elif option == "--module":
                check_lean_module_name(value)
                module = String(value)
            else:
                raise Error("unknown packet-square option")
        i += 1
    if format == "lean" and module.byte_length() == 0:
        raise Error("--format lean needs --module")
    if format == "jsonl" and module.byte_length() > 0:
        raise Error("--module applies only to --format lean")
    if format == "jsonl":
        print(budget_json(state_cap, length_cap, packet_cap, edge_cap))
    var bounded = build_bounded(sigma3(sigma), state_cap, length_cap)
    if not bounded.complete():
        if format == "jsonl":
            print(String('{"record":"inconclusive","budget_kind":') + String(bounded.exhausted) + '}')
        raise Error("BPA budget exhausted; no packet-square table")
    var sq = build_packet_square(sigma, bounded.graph, packet_cap, edge_cap, target)
    if format == "jsonl":
        emit_packet_square_jsonl(sq, hub_rows)
        return
    var command = (String("cd kernel && pixi run --locked mojo run -I . packet_square_export.mojo --sigma ")
                   + sigma_text(sigma) + " --target " + target_text
                   + " --state-cap " + String(state_cap) + " --length-cap " + String(length_cap)
                   + " --packet-cap " + String(packet_cap) + " --edge-cap " + String(edge_cap)
                   + " --format lean --module " + module + (" --hub-rows" if hub_rows else ""))
    emit_packet_square_lean(sq, module, hub_rows, command)
