"""Native exact selected-rank verifier: finite soundness, not closure coverage."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.perron_field3 import CubicElt
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapAutomaton, build_seed_overlap_tables,
)
from psc.selected_rank import (
    verify_rank_forest, verify_overlap_rank_witness, verify_complete_overlap_rank,
    verify_exact_closed_carrier, verify_closed_ranked_carrier,
)


def tiny_adjacency() -> List[List[Int]]:
    var adj = List[List[Int]]()
    var first: List[Int] = [1]
    var last = List[Int]()
    adj.append(first^)
    adj.append(last^)
    return adj^


def rejected_rank(
    adj: List[List[Int]],
    typed: List[Bool],
    ranks: List[Int],
    chosen: List[Int],
) -> Bool:
    try:
        _ = verify_rank_forest(adj, typed, ranks, chosen)
        return False
    except:
        return True


def small_sigma() -> List[List[Int]]:
    # Exact nonunit determinant-two calibration already used by the
    # repository's overlap_seed_patch regression.
    var sigma = List[List[Int]]()
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    sigma.append(a0^)
    sigma.append(a1^)
    sigma.append(a2^)
    return sigma^


def main() raises:
    var adj = tiny_adjacency()
    var typed: List[Bool] = [False, True]
    var ranks: List[Int] = [1, 0]
    var chosen: List[Int] = [0, -1]
    assert_equal(verify_rank_forest(adj, typed, ranks, chosen), 1)

    # These failures are mathematical soundness controls, not mere
    # serialization tests: false rank, missing chosen edge, inconsistent
    # terminal, forged child and incomplete array each refuse.
    assert_true(rejected_rank(adj, typed, [0, 0], chosen))
    assert_true(rejected_rank(adj, typed, [2, 0], chosen))
    assert_true(rejected_rank(adj, typed, ranks, [-1, -1]))
    assert_true(rejected_rank(adj, typed, ranks, [0, 0]))
    assert_true(rejected_rank(adj, typed, ranks, [0, -1, 2]))

    var malformed = List[List[Int]]()
    var wrong: List[Int] = [8]
    var empty = List[Int]()
    malformed.append(wrong^)
    malformed.append(empty^)
    assert_true(rejected_rank(malformed, typed, ranks, chosen))

    # A finite directed nonproductive self-cycle cannot carry a
    # decreasing selected-edge rank. Adding a coincidence elsewhere
    # does not make the cycle productive.
    var cyclic = List[List[Int]]()
    var loop: List[Int] = [0]
    var end = List[Int]()
    cyclic.append(loop^)
    cyclic.append(end^)
    assert_true(rejected_rank(cyclic, typed, ranks, chosen))

    # Bind a toy selected source to the ACTUAL exact cubic-field
    # substitution child at occurrence (0,0). The caller must still
    # establish completeness of all descendants independently.
    var tables = build_seed_overlap_tables(small_sigma())
    var states = List[OverlapState]()
    states.append(OverlapState(0, 1, CubicElt()))
    states.append(OverlapState(1, 0, CubicElt()))
    # For this sigma, sigma(0)[0]=1, sigma(1)[0]=0,
    # so the selected top/bottom child types are (1,0), not (0,0).
    var a = SeedOverlapAutomaton(states, adj, False)
    var tops: List[Int] = [0, -1]
    var bottoms: List[Int] = [0, -1]
    # The second vertex is NOT a typed coincidence. So an independently
    # constructed terminal mask cannot override the actual state test.
    var refused = False
    try:
        _ = verify_overlap_rank_witness(tables, a, ranks, chosen, tops, bottoms)
    except:
        refused = True
    assert_true(refused)

    var exact_states = List[OverlapState]()
    exact_states.append(OverlapState(0, 1, CubicElt()))
    exact_states.append(OverlapState(1, 0, CubicElt()))
    # Real source/child pair, but the selected target is nonterminal;
    # a fake rank-zero terminal must still fail closed.
    var exact_graph = SeedOverlapAutomaton(exact_states, adj, True)
    refused = False
    try:
        _ = verify_complete_overlap_rank(tables, exact_graph,
            ranks, chosen, tops, bottoms)
    except:
        refused = True
    assert_true(refused)

    # A positive ACTUAL indexed example from the same exact substitution.
    # sigma(1)[0]=0 and sigma(2)[0]=0, with zero initial shift,
    # so source (1,2,0) --(0,0)--> typed coincidence (0,0,0).
    var good_states = List[OverlapState]()
    good_states.append(OverlapState(1, 2, CubicElt()))
    good_states.append(OverlapState(0, 0, CubicElt()))
    var good = SeedOverlapAutomaton(good_states, adj, False)
    assert_equal(verify_overlap_rank_witness(
        tables, good, ranks, chosen, tops, bottoms), 1)
    # The complete wrapper refuses a truly capped instance. A fabricated
    # noncapped graph is not independently evidence of forward completeness.
    var capped = SeedOverlapAutomaton(good_states, adj, True)
    refused = False
    try:
        _ = verify_complete_overlap_rank(tables, capped,
            ranks, chosen, tops, bottoms)
    except:
        refused = True
    assert_true(refused)

    # Change one real selected bottom occurrence: sigma(2)[1]=0 too,
    # but its prefix shifts, so the resulting child is not zero-shift.
    var wrong_bottoms: List[Int] = [1, -1]
    refused = False
    try:
        _ = verify_overlap_rank_witness(tables, good,
            ranks, chosen, tops, wrong_bottoms)
    except:
        refused = True
    assert_true(refused)
    # A self-contained genuine typed coincidence is a valid, closed,
    # precisely audited finite carrier of one vertex.
    var only_terminal = List[OverlapState]()
    only_terminal.append(OverlapState(0, 0, CubicElt()))
    var no_edges = List[List[Int]]()
    var e = List[Int]()
    no_edges.append(e^)
    var singleton = SeedOverlapAutomaton(only_terminal, no_edges, False)
    var seeds = List[OverlapState]()
    seeds.append(OverlapState(0, 0, CubicElt()))
    assert_equal(verify_exact_closed_carrier(tables, singleton, seeds), 1)
    var zeros: List[Int] = [0]
    var empty_choice: List[Int] = [-1]
    assert_equal(verify_closed_ranked_carrier(
        tables, singleton, seeds, zeros, empty_choice,
        empty_choice, empty_choice), 0)

    # The two-vertex *locally sound* source->coincidence certificate
    # is not forward complete: the source (1,2,0) has additional
    # literal strict children. Merely declaring capped=False cannot
    # convert that incomplete table into a complete global proof.
    refused = False
    try:
        _ = verify_exact_closed_carrier(tables, good, good_states)
    except:
        refused = True
    assert_true(refused)

    # A required source omitted from an otherwise closed singleton
    # carrier must refuse the claimed all-seed coverage.
    var missing = List[OverlapState]()
    missing.append(OverlapState(1, 2, CubicElt()))
    refused = False
    try:
        _ = verify_exact_closed_carrier(tables, singleton, missing)
    except:
        refused = True
    assert_true(refused)

    print('SELECTED_RANK_NATIVE_LOCAL_SOUNDNESS_PASS')
    require_contract("finite listed-state selected-path rank soundness with genuine indexed overlap children and typed coincidence terminals; finite carrier controls reject missing seeds and escaping children; no universal forward closure, X-descendant productivity or PSC proof")
