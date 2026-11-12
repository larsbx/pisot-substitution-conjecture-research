"""Original graph payload, exact packed fields and fail-closed controls."""

from std.testing import assert_equal, assert_true
from finite_exact.bigint_z import BigZ, bigz_from_i64, bigz_add, bigz_mul
from finite_exact.exact_decimal import bigz_decimal
from mojo_smoke.claims import require_contract
from psc.c4_archived_payload import (
    state_code, orbit_key, slot_code, pack_archived_row,
    unpack_archived_fields, packed_rows, lookup_order,
)
from psc.c4_archived_graph_refinement import (
    ArchivedRefinement, build_archived_refinement, verify_archived_contraction,
)
from psc.c4_literal_inverse_binding import swap_packet
from psc.c4_pair_overlap_graph import construct_pair_weights, verify_pair_weights


def must_refuse(binding: ArchivedRefinement, weights: List[Int], name: String) raises:
    var refused = False
    try:
        _ = verify_archived_contraction(binding,weights)
        _ = packed_rows(binding,weights)
        _ = lookup_order(binding)
    except:
        refused = True
    assert_true(refused)
    print("rejected",name)


def main() raises:
    var root: List[Int] = [0,1,0,0,0]
    var empty = List[List[Int]]()
    var parallel: List[List[Int]] = [[1,0,1,1],[1,1,2,0]]
    var bits = pack_archived_row(root,1,[-1,-1],0,empty,3,0)
    assert_equal(bigz_decimal(bits),"4539059951108097")
    var repeated = pack_archived_row(root,1,[-1,-1],0,parallel,3,0)
    assert_equal(bigz_decimal(repeated),"5483081011333839697362526147398598657")
    var decoded = unpack_archived_fields(repeated)
    assert_equal(decoded[0][1],2)
    for k in range(2):
        for field in range(4):
            assert_equal(decoded[k+1][field],parallel[k][field])
    var field_controls = 0
    try:
        _ = pack_archived_row(root,0,[-1,-1],0,empty,3,0)
    except:
        field_controls += 1
    try:
        _ = pack_archived_row(root,1000001,[-1,-1],0,empty,3,0)
    except:
        field_controls += 1
    try:
        _ = pack_archived_row([0,1,33,0,0],1,[-1,-1],0,empty,3,0)
    except:
        field_controls += 1
    try:
        _ = pack_archived_row(root,1,[3,0],1,empty,4,3)
    except:
        field_controls += 1
    try:
        _ = pack_archived_row(root,1,[0,0],32,empty,4,3)
    except:
        field_controls += 1
    try:
        _ = slot_code([3,0,0,0],3)
    except:
        field_controls += 1
    try:
        _ = slot_code([0,15,0,0],3)
    except:
        field_controls += 1
    try:
        _ = slot_code([0,0,0,2],3)
    except:
        field_controls += 1
    var high = bigz_from_i64(1)
    for _ in range(80):
        high = bigz_mul(high,bigz_from_i64(2))
    try:
        _ = unpack_archived_fields(bigz_add(bits,high))
    except:
        field_controls += 1
    assert_equal(field_controls,9)

    var full_rows = 0
    var full_slots = 0
    var semantic_controls = 0
    for fixture in range(2):
        var binding = build_archived_refinement(fixture)
        var result = construct_pair_weights(binding.graph)
        var weights = result[0].copy()
        assert_true(verify_archived_contraction(binding,weights) > 0)
        var packed = packed_rows(binding,weights)
        var order = lookup_order(binding)
        assert_equal(len(order),len(binding.graph.states))
        for i in range(len(packed)):
            var fields = unpack_archived_fields(packed[i])
            assert_equal(fields[0][0],weights[i])
            assert_equal(fields[0][1],len(binding.slots[i]))
            assert_equal(fields[0][2],state_code(binding.graph.states[i]))
            assert_equal(fields[0][3],binding.births[i][0]+1)
            assert_equal(fields[0][4],binding.births[i][1]+1)
            assert_equal(fields[0][5],binding.depths[i])
            assert_equal(len(fields)-1,len(binding.slots[i]))
            for k in range(len(binding.slots[i])):
                for field in range(4):
                    assert_equal(fields[k+1][field],binding.slots[i][k][field])
            assert_equal(orbit_key(binding.graph.states[i]),orbit_key(swap_packet(binding.graph.states[i])))
            if i > 0:
                assert_true(orbit_key(binding.graph.states[order[i-1]]) < orbit_key(binding.graph.states[order[i]]))
        full_rows += len(packed)
        full_slots += binding.edges

        var victim = -1
        var missing = -1
        for row in range(len(binding.slots)):
            for k in range(len(binding.slots[row])):
                for j in range(k):
                    if binding.slots[row][j][0] == binding.slots[row][k][0]:
                        victim = row
                        missing = k
                        break
                if victim >= 0:
                    break
            if victim >= 0:
                break
        assert_true(victim >= 0)
        var bad = binding.copy()
        var targets = List[Int]()
        var slots = List[List[Int]]()
        for k in range(len(bad.slots[victim])):
            if k != missing:
                targets.append(bad.graph.rows[victim][k])
                slots.append(bad.slots[victim][k].copy())
        bad.graph.rows[victim] = targets^
        bad.slots[victim] = slots^
        assert_true(verify_pair_weights(bad.graph,weights) > 0)
        must_refuse(bad,weights,"omitted_repeated_edge_despite_valid_numeric_bound")
        semantic_controls += 1
        bad = binding.copy()
        bad.direction = 1
        must_refuse(bad,weights,"swapped_graph_direction")
        semantic_controls += 1
        bad = binding.copy()
        bad.radii = [24,12]
        must_refuse(bad,weights,"wrong_original_box")
        semantic_controls += 1
        bad = binding.copy()
        bad.births[3] = [-1,-1]
        must_refuse(bad,weights,"incomplete_inverse_ancestry")
        semantic_controls += 1
        bad = binding.copy()
        bad.graph.states[3] = bad.graph.states[4].copy()
        must_refuse(bad,weights,"graph_domain_mismatch")
        semantic_controls += 1
        bad = binding.copy()
        bad.slots[victim][0][3] = 1-bad.slots[victim][0][3]
        must_refuse(bad,weights,"flipped_packed_track_swap")
        semantic_controls += 1
        bad = binding.copy()
        bad.digits[0][7] += 1
        must_refuse(bad,weights,"changed_nested_local_address")
        semantic_controls += 1
        bad = binding.copy()
        bad.graph.fixture = 1-fixture
        must_refuse(bad,weights,"different_literal_substitution")
        semantic_controls += 1
        bad = binding.copy()
        var states = bad.graph.states.copy()
        _ = states.pop()
        bad.graph.states = states^
        var shortened = List[List[Int]]()
        for source in range(len(bad.graph.states)):
            var row = List[Int]()
            for target in bad.graph.rows[source]:
                if target < len(bad.graph.states):
                    row.append(target)
            shortened.append(row^)
        bad.graph.rows = shortened^
        must_refuse(bad,weights,"removed_ancestor_and_all_stored_graph_edges")
        semantic_controls += 1
    assert_equal(full_rows,14233)
    assert_equal(full_slots,69679)
    assert_equal(semantic_controls,18)
    print("archived payload full roundtrip",full_rows,full_slots)
    print("archived payload field and semantic refusals",field_controls,semantic_controls)
    require_contract("original two-source archived Lean payload preserves all 14233 states and 69679 positional slots, literal addresses, swap normalization, weights and rooted ancestry; exact bounded serialization and orbit-key lookup refuse corruption; native checks do not supply Lean proof terms or a C4/PSC conclusion")
