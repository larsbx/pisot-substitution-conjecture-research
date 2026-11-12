"""Negative controls for finite source binding, not geometric completeness."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_archived_graph_refinement import (
    ArchivedRefinement, build_archived_refinement, verify_archived_refinement,
    verify_archived_contraction, verify_archived_ordered_inventory,
)
from psc.c4_pair_overlap_graph import construct_pair_weights, verify_pair_weights, outside_pair_box


def must_refuse(binding: ArchivedRefinement, name: String) raises:
    var refused = False
    try:
        verify_archived_refinement(binding)
    except:
        refused = True
    assert_true(refused)
    print("rejected",name)


def main() raises:
    var sizes: List[Int] = [7150,7083]
    var counts: List[Int] = [34826,34853]
    var controls = 0
    for fixture in range(2):
        var original = build_archived_refinement(fixture)
        var result = construct_pair_weights(original.graph)
        var weights = result[0].copy()
        assert_equal(len(original.graph.states),sizes[fixture])
        assert_equal(original.edges,counts[fixture])
        assert_equal(len(original.digits),15)
        assert_true(original.swapped > 0)
        assert_true(original.repeated > 0)
        assert_true(verify_archived_contraction(original,weights) > 0)
        # Deleting an actual repeated positional edge preserves the numerical
        # upper-bound inequality.  Structural source authentication rejects it.
        var victim = -1
        var missing_position = -1
        for row in range(len(original.graph.rows)):
            for i in range(len(original.graph.rows[row])):
                for j in range(i):
                    if original.graph.rows[row][i] == original.graph.rows[row][j]:
                        victim = row
                        missing_position = i
                        break
                if victim >= 0:
                    break
            if victim >= 0:
                break
        assert_true(victim >= 0)
        var bad = original.copy()
        var short = List[Int]()
        for i in range(len(bad.graph.rows[victim])):
            if i != missing_position:
                short.append(bad.graph.rows[victim][i])
        bad.graph.rows[victim] = short^
        assert_true(verify_pair_weights(bad.graph,weights) > 0)
        must_refuse(bad,"omitted_repeated_positional_edge")
        controls += 1
        bad = original.copy()
        bad.direction = 1
        must_refuse(bad,"swapped_graph_direction")
        controls += 1
        bad = original.copy()
        bad.radii = [24,12]
        must_refuse(bad,"wrong_24_12_box")
        controls += 1
        bad = original.copy()
        bad.period = 1
        must_refuse(bad,"wrong_block_power")
        controls += 1
        bad = original.copy()
        bad.births[3] = [-1,-1]
        must_refuse(bad,"incomplete_inverse_ancestry")
        controls += 1
        bad = original.copy()
        bad.graph.states[3] = bad.graph.states[4].copy()
        must_refuse(bad,"graph_domain_mismatch")
        controls += 1
        bad = original.copy()
        bad.graph.fixture = 1-fixture
        must_refuse(bad,"different_original_substitution")
        controls += 1
        bad = original.copy()
        bad.digits[0][7] = 1
        must_refuse(bad,"wrong_nested_local_address")
        controls += 1
        bad = original.copy()
        bad.graph.residue_rejections += 1
        must_refuse(bad,"unjustified_residue_exclusion")
        controls += 1
        bad = original.copy()
        var row = 0
        while len(bad.slots[row]) == 0:
            row += 1
        bad.slots[row][0][3] = 1-bad.slots[row][0][3]
        must_refuse(bad,"flipped_track_swap")
        var refused = False
        try:
            verify_archived_ordered_inventory(bad)
        except:
            refused = True
        assert_true(refused)
        controls += 1
        bad = original.copy()
        var transposed = List[List[Int]]()
        for _ in range(len(original.graph.states)):
            transposed.append(List[Int]())
        for source in range(len(original.graph.rows)):
            for target in original.graph.rows[source]:
                transposed[target].append(source)
        bad.graph.rows = transposed^
        must_refuse(bad,"transposed_actual_rows")
        controls += 1
        bad = original.copy()
        var states = bad.graph.states.copy()
        _ = states.pop()
        bad.graph.states = states^
        var truncated = List[List[Int]]()
        for source in range(len(bad.graph.states)):
            var targets = List[Int]()
            for target in original.graph.rows[source]:
                if target < len(bad.graph.states):
                    targets.append(target)
            truncated.append(targets^)
        bad.graph.rows = truncated^
        must_refuse(bad,"removed_ancestor_and_all_stored_edges")
        controls += 1
        print("bound",fixture,len(original.graph.states),original.edges,original.swapped,original.repeated)
    assert_true(not outside_pair_box(32,0,16))
    assert_true(outside_pair_box(33,0,0))
    print("source-bound historical graph negative controls",controls)
    require_contract("source-bound two named 16,8 paired-occurrence graphs; all literal parent/flat/nested positions, exact residue and strict box exclusions, track-swap lift, repeated slots, rooted complete inverse ancestry and forward transpose; rejects numeric-only mutation acceptance; no all-strict-packet or C4/PSC conclusion")
