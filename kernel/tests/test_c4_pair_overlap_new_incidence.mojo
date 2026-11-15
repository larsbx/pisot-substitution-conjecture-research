"""Finite-carrier arithmetic, complete new-source graphs and failure controls."""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.closed_interval import IQ
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from mojo_smoke.claims import require_contract
from psc.c4_nonunit_residue_occupancy import same_vector
from psc.c4_pair_overlap_carrier import (
    CarrierBox, bounded_ceil, bounded_floor, canonical_pair, checked_carrier, contains_offset,
    enclose_inverse_chart, offset_key, typed_offset_key, validate_carrier,
)
from psc.c4_pair_overlap_new_incidence import (
    NewIncidenceGraph, authenticate_new_graph, build_new_incidence_graph,
    certify_uniform_upper_tenth, construct_new_weights, make_new_model,
    new_matrix, new_matrix_power, new_source_images, outside_new_box,
    verify_new_rate, verify_new_weights,
)


def test_integer_carrier_boundaries_and_keys() raises:
    assert_equal(bounded_floor(Q(-3,2)),-2)
    assert_equal(bounded_ceil(Q(-3,2)),-1)
    assert_equal(bounded_floor(Q(2,1)),2)
    assert_equal(bounded_ceil(Q(2,1)),2)
    var inverse = List[IQ]()
    for i in range(3):
        for j in range(3):
            inverse.append(IQ.singleton(q_int(1 if i == j else 0)))
    var axes: List[IQ] = [IQ(Q(-3,2),Q(3,2)),IQ(q_int(-2),q_int(-1)),IQ.singleton(Q.zero())]
    var box = enclose_inverse_chart(inverse,axes)
    assert_true(same_vector(box.lower,[-1,-2,0]))
    assert_true(same_vector(box.upper,[1,-1,0]))
    assert_equal(box.capacity,6)
    assert_true(contains_offset(box,[1,-1,0]))
    assert_false(contains_offset(box,[2,-1,0]))
    assert_equal(offset_key(box,[-1,-2,0]),0)
    assert_equal(offset_key(box,[1,-1,0]),5)
    assert_equal(typed_offset_key(box,0,0,[-1,-2,0]),0)
    assert_equal(typed_offset_key(box,2,2,[1,-1,0]),35)
    assert_true(same_vector(canonical_pair(2,0,1,-2,3),[0,2,-1,2,-3]))
    assert_true(same_vector(canonical_pair(1,1,0,0,1),[1,1,0,0,-1]))
    var refused = False
    try:
        _ = canonical_pair(2,0,Int.MIN,0,0)
    except:
        refused = True
    assert_true(refused)
    box.capacity += 1
    refused = False
    try:
        validate_carrier(box)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = enclose_inverse_chart(List[IQ](),axes)
    except:
        refused = True
    assert_true(refused)


def test_authenticated_new_model() raises:
    var model = make_new_model()
    assert_equal(model.capacity,178002)
    assert_true(same_vector(new_matrix().charpoly(),[-2,-3,-1,1]))
    assert_equal(new_matrix().det(),2)
    assert_true(same_vector(new_matrix_power(2).e,[2,2,1,2,4,3,2,1,1]))
    assert_true(same_vector(new_matrix_power(2).adjugate().e,[1,-1,2,4,0,-4,-6,2,4]))
    for box in model.carriers:
        assert_true(same_vector(box.lower,[-15,-14,-16]))
        assert_true(same_vector(box.upper,[15,14,16]))
        assert_equal(box.capacity,29667)
    assert_true(same_vector(new_source_images(11)[0],[1,1]))
    assert_true(same_vector(new_source_images(11)[1],[2,1,0]))
    assert_true(same_vector(new_source_images(11)[2],[1,0]))
    # Stable-boundary contact remains; the integer carrier is a distinct test.
    assert_false(outside_new_box([16,0,0]))
    assert_true(outside_new_box([17,0,0]))
    certify_uniform_upper_tenth()


def test_all_twelve_complete_certificates() raises:
    for index in range(12):
        var graph = build_new_incidence_graph(index)
        var result = construct_new_weights(graph)
        assert_true(result[1] > 0)
        assert_true(verify_new_weights(graph,result[0]) >= 125)
        for state in graph.states:
            assert_false(state[0] == state[1] and state[2] == 0 and state[3] == 0 and state[4] == 0)


def test_submitted_graph_and_weight_mutations() raises:
    var graph = build_new_incidence_graph(0)
    authenticate_new_graph(graph)
    var result = construct_new_weights(graph)
    var wrong = result[0].copy()
    wrong[0] = 0
    var refused = False
    try:
        _ = verify_new_weights(graph,wrong)
    except:
        refused = True
    assert_true(refused)
    var forged = graph.copy()
    var changed = False
    for i in range(len(forged.rows)):
        if not changed and len(forged.rows[i]) > 0:
            var replacement = List[Int]()
            for j in range(1,len(forged.rows[i])):
                replacement.append(forged.rows[i][j])
            forged.rows[i] = replacement^
            changed = True
    assert_true(changed)
    refused = False
    try:
        authenticate_new_graph(forged)
    except:
        refused = True
    assert_true(refused)
    forged = graph.copy()
    forged.states[0] = [0,0,0,0,0]
    refused = False
    try:
        authenticate_new_graph(forged)
    except:
        refused = True
    assert_true(refused)
    forged = graph.copy()
    forged.model.chart.a = IQ.singleton(Q.zero())
    refused = False
    try:
        authenticate_new_graph(forged)
    except:
        refused = True
    assert_true(refused)


def test_invalid_inputs_and_operational_budgets() raises:
    for index in [-1,12]:
        var refused = False
        try:
            _ = build_new_incidence_graph(index)
        except:
            refused = True
        assert_true(refused)
    var refused = False
    try:
        _ = build_new_incidence_graph(0,3)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_new_incidence_graph(0,20000,1,1)
    except:
        refused = True
    assert_true(refused)
    for numerator in [0,126]:
        refused = False
        try:
            verify_new_rate(numerator,20)
        except:
            refused = True
        assert_true(refused)
    var graph = build_new_incidence_graph(3)
    refused = False
    try:
        _ = construct_new_weights(graph,124,20,4000)
    except:
        refused = True
    assert_true(refused)  # Bounded search refusal, never nonproductivity.
    refused = False
    try:
        _ = construct_new_weights(graph,125,20,1)
    except:
        refused = True
    assert_true(refused)


def test_diagonal_same_occurrence_control() raises:
    var model = make_new_model()
    var states: List[List[Int]] = [[0,0,0,0,0],[1,1,0,0,0],[2,2,0,0,0]]
    var rows = List[List[Int]]()
    var square = new_matrix_power(2)
    # This is the actual same-occurrence diagonal subgraph M^2, not a claim
    # to be the complete shifted-overlap graph.  Its Perron root is beta^2.
    for first in range(3):
        var row = List[Int]()
        for second in range(3):
            for _ in range(square.at(first,second)):
                row.append(second)
        rows.append(row^)
    var graph = NewIncidenceGraph(0,model,states,rows,0,0,0)
    var refused = False
    try:
        _ = construct_new_weights(graph,125,20,4000)
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_integer_carrier_boundaries_and_keys()
    test_authenticated_new_model()
    test_all_twelve_complete_certificates()
    test_submitted_graph_and_weight_mutations()
    test_invalid_inputs_and_operational_budgets()
    test_diagonal_same_occurrence_control()
    print("[PASS] finite typed carriers, twelve new incidence graphs, exact positive weights and refusal controls")
    require_contract("Complete twelve-source x^3-x^2-3x-2 paired-occurrence graphs with authenticated chart and box, proved finite typed carriers, strict rational subinvariance, preserved multiplicities and bounded refusal")
