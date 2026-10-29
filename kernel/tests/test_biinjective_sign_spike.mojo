"""Compile and run the real spike, and guard its explicit graph-copy semantics."""

from std.testing import assert_equal, assert_false, assert_true
from biinjective_sign_spike import main as run_spike, MAX_BPA_STATES, MAX_STATE_LENGTH
from mojo_smoke.claims import require_contract
from psc.bounded_bpa import BUDGET_LENGTH, BUDGET_STATES, build_bounded
from psc.bpa import recurrent_noncoincident_sccs
from psc.carrier import profile_component
from psc.endpoint_sign_spike import BRANCH_B, audit_closed_component
from psc.symmetry import parse_substitution_key
from substitution_dynamics.substitution import Substitution


def test_complete_copy_is_independent() raises:
    # Existing primitive, reducible, bi-injective Branch-B countercontrol.
    var sigma = parse_substitution_key("102/210/021")
    var bounded = build_bounded(Substitution.checked(sigma), MAX_BPA_STATES, MAX_STATE_LENGTH)
    assert_true(bounded.complete())
    var graph = bounded.graph.copy()
    assert_equal(graph.size(), 6)
    assert_equal(graph.alphabet, bounded.graph.alphabet)
    assert_equal(graph.capped, bounded.graph.capped)
    for i in range(graph.size()):
        assert_equal(graph.states[i].key(), bounded.graph.states[i].key())
        assert_equal(graph.adj[i], bounded.graph.adj[i])
    var comps = recurrent_noncoincident_sccs(graph)
    var closed = 0
    for ci in range(len(comps)):
        if not profile_component(graph, comps[ci]).is_sink():
            continue
        var info = audit_closed_component(sigma, graph, comps[ci])
        assert_equal(info.branch, BRANCH_B)
        assert_equal(info.states, 3)
        assert_equal(info.occurrences, 9)
        assert_false(info.has_endpoint_diagonal)
        closed += 1
    assert_equal(closed, 1)
    # The current analyses borrow the graph. An owned copy must also permit
    # mutation without aliasing either nested list or the source's metadata.
    var source_key = bounded.graph.states[0].key()
    var source_edges = len(bounded.graph.adj[0])
    graph.states[0].u[0] = (graph.states[0].u[0] + 1) % 3
    graph.adj[0].append(0)
    graph.capped = True
    assert_true(graph.states[0].key() != source_key)
    assert_equal(len(graph.adj[0]), source_edges + 1)
    assert_equal(bounded.graph.states[0].key(), source_key)
    assert_equal(len(bounded.graph.adj[0]), source_edges)
    assert_true(bounded.complete())


def test_copy_preserves_budget_refusal() raises:
    var sigma = Substitution.checked(parse_substitution_key("102/210/021"))
    for budget in [BUDGET_STATES, BUDGET_LENGTH]:
        var bounded = build_bounded(
            sigma, 1 if budget == BUDGET_STATES else MAX_BPA_STATES,
            1 if budget == BUDGET_LENGTH else MAX_STATE_LENGTH,
        )
        assert_equal(bounded.exhausted, budget)
        assert_false(bounded.complete())
        var graph = bounded.graph.copy()
        assert_true(graph.capped)
        var refused = False
        try:
            _ = recurrent_noncoincident_sccs(graph)
        except:
            refused = True
        assert_true(refused)


def main() raises:
    test_complete_copy_is_independent()
    test_copy_preserves_budget_refusal()
    # Call the production entry point: reverting its copy repair must fail
    # compilation here, even though the independent fixture still compiles.
    run_spike()
    require_contract("biinjective spike compiles and executes its full finite scan; explicit graph copying preserves states, adjacency, metadata, Branch-B countercontrol and both budget refusals without aliasing nested mutations")
