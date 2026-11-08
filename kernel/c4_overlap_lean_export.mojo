"""Emit one canonical source graph as kernel-checkable Lean tree data.

No numerical summary replaces a row. The generated program re-emits the full
packet so the independent Python oracle can compare all occurrences again.
"""
from std.sys import argv
from psc.c4_pair_overlap_attractor import build_source_order_graph, construct_attractor_weights
from psc.c4_pair_overlap_graph import PairGraph
from finite_exact.bigint_z import BigZ, bigz_from_i64, bigz_add, bigz_mul
from finite_exact.exact_decimal import bigz_decimal


def lean_row(row: List[Int]) -> String:
    var line = String("[")
    for j in row:
        line += String(j)+String(",")
    return line+String("]")


def pack_row(state: List[Int], weight: Int, row: List[Int]) raises -> BigZ:
    if len(state) != 5 or weight < 1 or weight > 1000000 or len(row) >= 1024:
        raise Error("Lean packed row shape or field budget")
    if state[0] < 0 or state[0] > 2 or state[1] < 0 or state[1] > 2:
        raise Error("Lean packed row letter domain")
    for i in range(2,5):
        if state[i] < -40 or state[i] > 40:
            raise Error("Lean packed row coordinate budget")
    var bits = BigZ()
    for pos in range(len(row)-1,-1,-1):
        if row[pos] < 0 or row[pos] >= 16384:
            raise Error("Lean packed target does not fit; no truncation")
        bits = bigz_add(bigz_mul(bits,bigz_from_i64(16384)),bigz_from_i64(Int64(row[pos])))
    var code = state[0]+4*state[1]+16*(state[2]+64)+2048*(state[3]+64)+262144*(state[4]+64)
    bits = bigz_add(bigz_mul(bits,bigz_from_i64(33554432)),bigz_from_i64(Int64(code)))
    bits = bigz_add(bigz_mul(bits,bigz_from_i64(1024)),bigz_from_i64(Int64(len(row))))
    return bigz_add(bigz_mul(bits,bigz_from_i64(1048576)),bigz_from_i64(Int64(weight)))


def emit_table(graph: PairGraph, weights: List[Int], start: Int, count: Int) raises:
    if count < 1 or start < 0 or start+count > len(graph.states):
        raise Error("Lean table export bounds")
    if count == 1:
        var bits = pack_row(graph.states[start],weights[start],graph.rows[start])
        print("    Table.leaf",bigz_decimal(bits))
    else:
        var left = count//2
        print("    Table.branch",left,"(")
        emit_table(graph,weights,start,left)
        print("    ) (")
        emit_table(graph,weights,start+left,count-left)
        print("    )")


def table_name(start: Int, count: Int) -> String:
    return String("rows_")+String(start)+String("_")+String(count)


def emit_chunks(graph: PairGraph, weights: List[Int], start: Int, count: Int) raises:
    if count <= 32:
        print(String("def ")+table_name(start,count)+String(" : Table Nat :="))
        emit_table(graph,weights,start,count)
    else:
        var left = count//2
        emit_chunks(graph,weights,start,left)
        emit_chunks(graph,weights,start+left,count-left)
        print(String("def ")+table_name(start,count)+String(" : Table Nat :="))
        print("    Table.branch",left,table_name(start,left),table_name(start+left,count-left))


def check_name(start: Int, count: Int) -> String:
    return String("checked_")+String(start)+String("_")+String(count)


def emit_checks(start: Int, count: Int) raises:
    var decl = String("theorem ")+check_name(start,count)+String(" : packet.checkRange ")+String(start)+String(" ")+String(count)+String(" = true := ")
    if count <= 32:
        print(decl+String("by decide +kernel"))
    else:
        var left = count//2
        emit_checks(start,left)
        emit_checks(start+left,count-left)
        print(decl+String("packet.checkRange_append ")+String(start)+String(" ")+String(left)+String(" ")+String(count-left)+String(" ")+check_name(start,left)+String(" ")+check_name(start+left,count-left))


def main() raises:
    var args = argv()
    if len(args) != 2:
        raise Error("usage: c4_overlap_lean_export.mojo SOURCE_INDEX (0..17)")
    var index = Int(args[1])
    var graph = build_source_order_graph(index)
    var result = construct_attractor_weights(graph,4000)
    var weights = result[0].copy()
    print("import PscVerif.OverlapPacket")
    print("import Lean.Util.CollectAxioms")
    print("set_option maxRecDepth 1000000")
    print("set_option Elab.async false")
    print("set_option maxHeartbeats 0")
    print("open PscVerif.OverlapPacket")
    print(String("namespace PscVerif.OverlapGenerated.Source")+String(index))
    emit_chunks(graph,weights,0,len(graph.states))
    print("def packet : Packet where")
    print("  source :=",index)
    print("  residueRejections :=",graph.residue_rejections)
    print("  boxRejections :=",graph.box_rejections)
    print("  sweeps :=",result[1])
    print("  count :=",len(graph.states))
    print("  table :=",table_name(0,len(graph.states)))
    print("theorem header_checked : packet.HeaderValid := by decide +kernel")
    emit_checks(0,len(graph.states))
    print(String("theorem accepted : packet.check = true := packet.check_iff.mpr (packet.valid_of_range header_checked ")+check_name(0,len(graph.states))+String(")"))
    print("theorem typed_accepted : (packet.toCertificate (packet.check_iff.mp accepted)).check = true := packet.toCertificate_check (packet.check_iff.mp accepted)")
    print("def emit : IO Unit := Packet.emit packet")
    print(String("end PscVerif.OverlapGenerated.Source")+String(index))
