"""Emit one original sharp-box archive as source-bound Lean proof data."""

from std.sys import argv
from finite_exact.bigint_z import BigZ
from finite_exact.exact_decimal import bigz_decimal
from psc.c4_archived_graph_refinement import (
    ArchivedRefinement, build_archived_refinement, verify_archived_contraction,
)
from psc.c4_pair_overlap_graph import construct_pair_weights
from psc.c4_archived_payload import packed_rows, lookup_order, orbit_key, emit_archived_payload


def table_name(start: Int, count: Int) -> String:
    return String("rows_")+String(start)+String("_")+String(count)


def emit_table(rows: List[BigZ], start: Int, count: Int) raises:
    if count < 1 or start < 0 or start+count > len(rows):
        raise Error("archived Lean table export bounds")
    if count == 1:
        print("    PscVerif.OverlapPacket.Table.leaf",bigz_decimal(rows[start]))
    else:
        var left = count//2
        print("    PscVerif.OverlapPacket.Table.branch",left,"(")
        emit_table(rows,start,left)
        print("    ) (")
        emit_table(rows,start+left,count-left)
        print("    )")


def emit_chunks(rows: List[BigZ], start: Int, count: Int) raises:
    if count <= 32:
        print(String("def ")+table_name(start,count)+String(" : PscVerif.OverlapPacket.Table Nat :="))
        emit_table(rows,start,count)
    else:
        var left = count//2
        emit_chunks(rows,start,left)
        emit_chunks(rows,start+left,count-left)
        print(String("def ")+table_name(start,count)+String(" : PscVerif.OverlapPacket.Table Nat :="))
        print("    PscVerif.OverlapPacket.Table.branch",left,table_name(start,left),table_name(start+left,count-left))


def lookup_name(start: Int, count: Int) -> String:
    return String("lookup_")+String(start)+String("_")+String(count)


def emit_lookup(binding: ArchivedRefinement, order: List[Int], start: Int, count: Int) raises:
    if count < 0 or start < 0 or start+count > len(order):
        raise Error("archived Lean lookup export bounds")
    if count == 0:
        print("    Lookup.empty")
        return
    var left = count//2
    var row = order[start+left]
    print("    Lookup.node",orbit_key(binding.graph.states[row]),row,"(")
    emit_lookup(binding,order,start,left)
    print("    ) (")
    emit_lookup(binding,order,start+left+1,count-left-1)
    print("    )")


def emit_lookup_chunks(binding: ArchivedRefinement, order: List[Int], start: Int, count: Int) raises:
    if count <= 32:
        print(String("def ")+lookup_name(start,count)+String(" : Lookup :="))
        emit_lookup(binding,order,start,count)
    else:
        var left = count//2
        emit_lookup_chunks(binding,order,start,left)
        emit_lookup_chunks(binding,order,start+left+1,count-left-1)
        var row = order[start+left]
        print(String("def ")+lookup_name(start,count)+String(" : Lookup :="))
        print("    Lookup.node",orbit_key(binding.graph.states[row]),row,lookup_name(start,left),lookup_name(start+left+1,count-left-1))


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


def emit_consumers():
    print("open Set MeasureTheory")
    print("open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceGraphBinding")
    print("open Psc.OccurrencePiece Psc.OccurrenceResidue Psc.OccurrenceAdmissibility")
    print("open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedProductHaar")
    print("open Psc.ArchivedGraphRefinement")
    print("theorem domain_iff (u : OccurrenceTransport.Packet) :")
    print("    (u ∈ orderedLift packet.states ∧")
    print("      (overlap (ambientStar (substitution packet.fixture) piZ) (tiles packet.fixture) u).Nonempty) ↔")
    print("    (Ancestry (iterateImages (substitution packet.fixture) 2) ArchivedRoot u ∧")
    print("      (overlap (ambientStar (substitution packet.fixture) piZ) (tiles packet.fixture) u).Nonempty) :=")
    print("  packet.rooted_nonempty_domain_iff valid u")
    print("theorem roots_null (ν : Measure (H (substitution packet.fixture)))")
    print("    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :")
    print("    ∀ k, (volume.prod ν)")
    print("      (overlap (ambientStar (substitution packet.fixture) piZ) (tiles packet.fixture) (archivedRoot k)) = 0 :=")
    print("  packet.roots_null valid ν")
    print("theorem ancestors_null (ν : Measure (H (substitution packet.fixture)))")
    print("    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]")
    print("    (u : OccurrenceTransport.Packet)")
    print("    (hu : Ancestry (iterateImages (substitution packet.fixture) 2) ArchivedRoot u) :")
    print("    (volume.prod ν)")
    print("      (overlap (ambientStar (substitution packet.fixture) piZ) (tiles packet.fixture) u) = 0 :=")
    print("  packet.ancestors_null valid ν u hu")
    print("theorem no_strict_system (C : Finset Psc.OccurrenceTransport.WordPair) :")
    print("    ¬ Psc.StrictSystem.StrictSystem (substitution packet.fixture) C :=")
    print("  packet.no_strictSystem valid C")
    print("theorem seed_terminates {T : Psc.OccurrenceTransport.WordPair}")
    print("    (hT : T ∈ (Psc.Descendants.seeds : Finset Psc.OccurrenceTransport.WordPair)) :")
    print("    Psc.StrictSystem.TerminatesWithCoincidence (substitution packet.fixture) T :=")
    print("  packet.seed_terminates valid hT")
    print("theorem reachable_terminates {T : Psc.OccurrenceTransport.WordPair}")
    print("    (hT : T ∈ Psc.Descendants.bpaStatesNC (substitution packet.fixture)) :")
    print("    Psc.StrictSystem.TerminatesWithCoincidence (substitution packet.fixture) T :=")
    print("  packet.reachable_terminates valid hT")


def main() raises:
    var args = argv()
    if len(args) != 2:
        raise Error("usage: c4_archived_lean_export.mojo FIXTURE (0 or 1) | packet")
    if args[1] == "packet":
        print("schema c4-archived-payload-v1")
        for fixture in range(2):
            var binding = build_archived_refinement(fixture)
            var result = construct_pair_weights(binding.graph)
            emit_archived_payload(binding,result[0],result[1])
        return
    var fixture = Int(args[1])
    if fixture < 0 or fixture > 1:
        raise Error("original named archived fixture required")
    var binding = build_archived_refinement(fixture)
    var result = construct_pair_weights(binding.graph)
    var weights = result[0].copy()
    var gap = verify_archived_contraction(binding,weights)
    var rows = packed_rows(binding,weights)
    var order = lookup_order(binding)
    var size = len(rows)
    var maximum_depth = 0
    for depth in binding.depths:
        if depth > maximum_depth:
            maximum_depth = depth
    print("import PscVerif.ArchivedPayloadConsumer")
    print("import PscVerif.NamedStrictExclusion")
    print("import PscVerif.NamedForwardCarrier")
    print("set_option maxRecDepth 1000000")
    print("set_option Elab.async false")
    print("set_option maxHeartbeats 0")
    print("open Psc.ArchivedPayload")
    print(String("namespace Psc.ArchivedPayloadGenerated.Source")+String(fixture))
    emit_chunks(rows,0,size)
    emit_lookup_chunks(binding,order,0,size)
    print("def packet : Psc.ArchivedPayload.Packet where")
    print("  fixture :=",fixture)
    print("  count :=",size)
    print("  table :=",table_name(0,size))
    print("  index :=",lookup_name(0,size))
    print("  power := 2")
    print("  boxX := 16")
    print("  boxY := 8")
    print("  direction := 0")
    print("  numerator :=",99 if fixture == 0 else 101)
    print("  residueRejections :=",binding.graph.residue_rejections)
    print("  boxRejections :=",binding.graph.box_rejections)
    print("  edges :=",binding.edges)
    print("  swapped :=",binding.swapped)
    print("  repeated :=",binding.repeated)
    print("  maxDepth :=",maximum_depth)
    print("  sweeps :=",result[1])
    print("  minimumGap :=",gap)
    print("theorem header_checked : packet.HeaderValid := by decide +kernel")
    emit_checks(0,size)
    print(String("theorem valid : packet.Valid := packet.valid_of_range header_checked ")+check_name(0,size))
    print("theorem accepted : packet.check = true := packet.check_iff.mpr valid")
    print("theorem typed_accepted : (packet.toCertificate valid).check = true := packet.toCertificate_check valid")
    emit_consumers()
    print(String("end Psc.ArchivedPayloadGenerated.Source")+String(fixture))
