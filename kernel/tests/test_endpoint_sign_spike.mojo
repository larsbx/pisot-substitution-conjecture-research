"""Exact endpoint-map and signed-state regressions for the exploratory spike."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.endpoint_sign_spike import (
    BRANCH_A, BRANCH_B, BRANCH_C, SpikeTotals, audit_closed_component,
    audit_specimen, endpoint_diagonal, injective, profile_key,
)
from psc.bpa import build, recurrent_noncoincident_sccs, apply_substitution, decompose
from psc.carrier import profile_component
from psc.words import Pair
from psc.symmetry import parse_substitution_key


def test_endpoint_profile_and_permutations() raises:
    assert_true(injective([2, 0, 1]))
    assert_false(injective([1, 1, 2]))
    var u: List[Int] = [0, 1]
    var v: List[Int] = [1, 0]
    var pair = Pair(u, v)
    assert_equal(profile_key(pair, 3), 0 * 27 + 1 * 9 + 1 * 3 + 0)
    assert_false(endpoint_diagonal(pair, [0, 2, 1], [1, 0, 2]))
    assert_true(endpoint_diagonal(pair, [0, 0, 2], [1, 0, 2]))


def test_trial_8381_is_not_per_state_immediate_productivity() raises:
    # Original 1-based sigma: 1->132, 2->32, 3->21.
    # Original state ((2,3),(3,2)); output 3221 versus 2132.
    # This negative control does not rely on a classification or eigenvalue.
    var sigma = parse_substitution_key("021/21/10")
    var u: List[Int] = [1, 2]
    var v: List[Int] = [2, 1]
    var top = apply_substitution(sigma, u)
    var bottom = apply_substitution(sigma, v)
    assert_equal(top, [2, 1, 1, 0])
    assert_equal(bottom, [1, 0, 2, 1])
    var parts = decompose(top, bottom)
    assert_equal(len(parts), 1)
    assert_false(parts[0].is_coincidence())


def test_trial_8381_component_is_branch_b_but_gauge_vacuous() raises:
    # Independently cross-checked by a direct small BPA factorization oracle:
    # 11 reachable states, one noncoincident-closed recurrent component of
    # size 3, all five within-SCC child occurrences oriented negatively.
    # This is period-one phase -1 (phase bit 1), hence Branch B.
    var sigma = parse_substitution_key("021/21/10")
    var graph = build(sigma, 20000)
    assert_false(graph.capped)
    assert_equal(graph.size(), 11)
    var comps = recurrent_noncoincident_sccs(graph)
    var seen = 0
    for ci in range(len(comps)):
        if not profile_component(graph, comps[ci]).is_sink():
            continue
        var record = audit_closed_component(sigma, graph, comps[ci])
        assert_equal(record.states, 3)
        assert_equal(record.occurrences, 5)
        assert_equal(record.branch, BRANCH_B)
        assert_true(record.direct_producer)
        assert_true(record.has_endpoint_diagonal)
        assert_true(record.endpoint_gauge)
        # Critical: the positive gauge result is *vacuous* here because all
        # three external endpoint profiles are distinct.
        assert_false(record.has_duplicate_profiles)
        seen += 1
    assert_equal(seen, 1)


def test_biinjective_reducible_primitive_has_a_branch_b_scc() raises:
    # 0->102, 1->210, 2->021 is primitive, with incidence M = all-ones,
    # characteristic polynomial t^2(t-3). Both endpoint maps are
    # permutations, yet the exact six-state BPA has a closed, recurrent
    # Branch-B SCC of size three with no endpoint-diagonal state.
    # Hence primitive + bi-injective does NOT exclude Branch B:
    # irreducibility/Pisot is a genuinely load-bearing hypothesis.
    var sigma = parse_substitution_key("102/210/021")
    assert_true(injective([1, 2, 0]))
    assert_true(injective([2, 0, 1]))
    var graph = build(sigma, 20000)
    assert_false(graph.capped)
    assert_equal(graph.size(), 6)
    var comps = recurrent_noncoincident_sccs(graph)
    var found = 0
    for ci in range(len(comps)):
        if not profile_component(graph, comps[ci]).is_sink():
            continue
        var result = audit_closed_component(sigma, graph, comps[ci])
        assert_equal(result.branch, BRANCH_B)
        assert_equal(result.states, 3)
        assert_equal(result.occurrences, 9)
        assert_false(result.has_endpoint_diagonal)
        assert_false(result.has_duplicate_profiles)
        found += 1
    assert_equal(found, 1)


def test_tribonacci_closed_scc_is_not_a_strict_carrier() raises:
    var sigma = parse_substitution_key("01/02/0")
    var graph = build(sigma, 20000)
    assert_false(graph.capped)
    var comps = recurrent_noncoincident_sccs(graph)
    var closed = 0
    var tally = SpikeTotals()
    audit_specimen(sigma, 20000, "tribonacci", tally, False)
    assert_equal(tally.visited, 1)
    assert_equal(tally.capped, 0)
    for ci in range(len(comps)):
        if not profile_component(graph, comps[ci]).is_sink():
            continue
        closed += 1
        var result = audit_closed_component(sigma, graph, comps[ci])
        assert_true(result.branch == BRANCH_A or result.branch == BRANCH_B or result.branch == BRANCH_C)
        assert_true(result.direct_producer)
    assert_equal(tally.closed, closed)


def test_bi_injective_endpoint_control_has_no_endpoint_diagonal() raises:
    var sigma = parse_substitution_key("01/12/20")
    # Endpoint maps 0,1,2 and 1,2,0 are both permutations.
    var p: List[Int] = [0, 1, 2]
    var q: List[Int] = [1, 2, 0]
    assert_true(injective(p))
    assert_true(injective(q))
    var u: List[Int] = [0, 1]
    var v: List[Int] = [1, 0]
    assert_false(endpoint_diagonal(Pair(u, v), p, q))


def main() raises:
    test_endpoint_profile_and_permutations()
    print("[PASS] endpoint profiles preserve all four ordered letters")
    test_trial_8381_is_not_per_state_immediate_productivity()
    print("[PASS] trial 8381 refutes per-state Branch-B productivity")
    test_trial_8381_component_is_branch_b_but_gauge_vacuous()
    print("[PASS] trial 8381: Branch B but endpoint-gauge success is vacuous")
    test_biinjective_reducible_primitive_has_a_branch_b_scc()
    print("[PASS] primitive bi-injective non-PIP Branch B counterexample")
    test_tribonacci_closed_scc_is_not_a_strict_carrier()
    print("[PASS] exact SCC child signing and closure flags")
    test_bi_injective_endpoint_control_has_no_endpoint_diagonal()
    print("[PASS] bi-injective ends exclude only endpoint diagonals")
    require_contract("endpoint-sign spike classifies complete noncoincident-closed recurrent BPA SCCs by exact signed occurrences, retains capped status, tests endpoint-only gauge factorization, and preserves the trial-8381 negative control without a universal claim")
