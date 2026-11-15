"""Actual incoming marks, ordered lifts, discovery witnesses and corruptions."""

from std.testing import assert_equal, assert_true
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.c4_literal_inverse_binding import (
    LiteralInverseBinding, authenticate_literal_binding, build_literal_binding,
    exact_inverse_ancestor, packet_key, swap_packet, verify_literal_binding,
)
from psc.c4_pair_overlap_new_incidence import new_matrix_power


def reject_binding(binding: LiteralInverseBinding) raises:
    var refused = False
    try:
        verify_literal_binding(binding)
    except:
        refused = True
    assert_true(refused)


def test_complete_source_class() raises:
    var states = 0
    var edges = 0
    var swapped = 0
    var repeated = 0
    for source in range(12):
        var binding = build_literal_binding(source)
        assert_equal(len(binding.digits),18)
        assert_true(binding.swapped > 0)
        assert_true(binding.repeated > 0)
        states += len(binding.graph.states)
        edges += binding.edges
        swapped += binding.swapped
        repeated += binding.repeated
        for i in range(3,len(binding.births)):
            assert_true(binding.births[i][0] >= 0 and binding.births[i][0] < i)
        print("[SOURCE]",source,len(binding.graph.states),binding.edges,binding.swapped,binding.repeated)
    assert_equal(states,43915)
    assert_equal(edges,253395)
    assert_equal(swapped,118583)
    assert_equal(repeated,24583)
    print("[COUNTS]",12,states,edges,2*states,2*edges,swapped,repeated,states-36)


def test_literal_identity_mutations() raises:
    var binding = build_literal_binding(0)
    # Public acceptance additionally reconstructs the unchanged historical graph.
    authenticate_literal_binding(binding)
    assert_equal(len(binding.graph.states),3664)
    assert_equal(binding.edges,21151)
    assert_equal(binding.swapped,9971)
    assert_equal(binding.repeated,2201)
    assert_equal(binding.slots[0][0][0],0)
    assert_equal(binding.slots[0][0][1],0)
    assert_equal(binding.slots[0][0][2],6)
    assert_equal(binding.slots[0][0][3],0)

    var forged = binding.copy()
    forged.images[0][0] = 0
    reject_binding(forged)
    forged = binding.copy()
    forged.words[0][0] = (forged.words[0][0]+1)%3
    reject_binding(forged)
    forged = binding.copy()
    forged.digits[0][0] = (forged.digits[0][0]+1)%3
    reject_binding(forged)
    forged = binding.copy()
    forged.digits[0][2] = 1
    reject_binding(forged)
    forged = binding.copy()
    forged.digits[0][3] += 1
    reject_binding(forged)
    forged = binding.copy()
    forged.slots[0][0][3] = 1
    reject_binding(forged)
    forged = binding.copy()
    var top = forged.slots[0][0][1]
    forged.slots[0][0][1] = forged.slots[0][0][2]
    forged.slots[0][0][2] = top
    reject_binding(forged)

    # Duplicate a different occurrence with exactly the SAME target.  Adjacency
    # counts and every old target id remain unchanged, yet the marks are wrong.
    forged = binding.copy()
    var changed = False
    for row in range(len(forged.slots)):
        if changed:
            break
        for j in range(len(forged.slots[row])):
            if changed:
                break
            for k in range(j):
                if forged.slots[row][j][0] == forged.slots[row][k][0]:
                    forged.slots[row][j] = forged.slots[row][k].copy()
                    changed = True
                    break
    assert_true(changed)
    reject_binding(forged)

    forged = binding.copy()
    var remaining = List[List[Int]]()
    for j in range(1,len(forged.slots[0])):
        remaining.append(forged.slots[0][j].copy())
    forged.slots[0] = remaining^
    reject_binding(forged)
    forged = binding.copy()
    forged.births[3] = [3,0]  # Circular birth is not an ancestry witness.
    reject_binding(forged)
    forged = binding.copy()
    forged.births[0] = [0,0]  # Root identity is explicit.
    reject_binding(forged)
    forged = binding.copy()
    forged.edges -= 1
    reject_binding(forged)

    # Mutating the old adjacency itself cannot hide an omitted internal edge.
    forged = binding.copy()
    var row_without_first = List[Int]()
    for j in range(1,len(forged.graph.rows[0])):
        row_without_first.append(forged.graph.rows[0][j])
    forged.graph.rows[0] = row_without_first^
    reject_binding(forged)
    forged = binding.copy()
    forged.graph.states[3] = forged.graph.states[0].copy()
    reject_binding(forged)
    print("[MUTATIONS]",14)


def test_integral_and_bounded_refusals() raises:
    var binding = build_literal_binding(0)
    var square = new_matrix_power(2)
    var adjugate = square.adjugate()
    var found_nonintegral = False
    var found_nonzero = False
    for row in range(len(binding.graph.states)):
        if found_nonintegral and found_nonzero:
            break
        var state = binding.graph.states[row].copy()
        for top in binding.digits:
            if top[0] != state[0]:
                continue
            for bottom in binding.digits:
                if bottom[0] != state[1]:
                    continue
                var raw = exact_inverse_ancestor(state,top,bottom,square,adjugate)
                if len(raw) == 0:
                    found_nonintegral = True
                elif raw[2] != 0 or raw[3] != 0 or raw[4] != 0:
                    found_nonzero = True
                    # A zero numerator matrix proposes the rounded ancestor 0.
                    # Rechecking M²*y=rhs refuses that forged inverse procedure.
                    var zero = Mat3([0,0,0,0,0,0,0,0,0])
                    var refused = False
                    try:
                        _ = exact_inverse_ancestor(state,top,bottom,square,zero)
                    except:
                        refused = True
                    assert_true(refused)
    assert_true(found_nonintegral)
    assert_true(found_nonzero)
    var refused = False
    try:
        _ = exact_inverse_ancestor(binding.graph.states[0],binding.digits[6],binding.digits[0],square,adjugate)
    except:
        refused = True
    assert_true(refused)
    for source in [-1,12]:
        refused = False
        try:
            _ = build_literal_binding(source)
        except:
            refused = True
        assert_true(refused)
    refused = False
    try:
        _ = build_literal_binding(0,3)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = packet_key([0,1,65,0,0])
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = swap_packet([0,1,Int.MIN,0,0])
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_complete_source_class()
    test_literal_identity_mutations()
    test_integral_and_bounded_refusals()
    print("[PASS] literal inverse rows, exact ordered forward inventory, transpose, well-founded births and corruptions")
    require_contract("Twelve-source literal sigma-squared inverse occurrences with exact integral marks, complete internal positional inventories, normalized ordered lifts, transpose counts and well-founded discovery witnesses")
