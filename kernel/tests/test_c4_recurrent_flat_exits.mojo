"""Literal recurrent flat PIP rows with outgoing mass and a productive exit."""

from std.testing import assert_equal, assert_true, assert_false
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.bounded_bpa import build_bounded
from psc.bpa import (
    apply_substitution, coincidence_boundaries, decompose, normalise,
    newborn_sync_positions, sigma3, substitution_incidence,
)
from psc.c4_complete_cone_hub_audit import audit_complete_strict_cones
from psc.c4_cut_alignment import classify_irreducible_birth
from psc.c4_two_generation_rank import _rank_det, literal_two_generation_parikh_rank
from psc.carrier import profile_component
from psc.pisot import is_pip
from psc.words import Pair, parikh
from substitution_dynamics.automaton import recurrent_noncoincident_sccs


def test_recurrent_flat_row_with_two_exits() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 2, 0]]
    var m = Mat3(substitution_incidence(sigma))
    assert_equal(m.charpoly(), [1, -1, -2, 1])
    assert_true(is_pip(m))

    # Actual interior good-edge witness with equal prefix masses at depth 4.
    var a: List[Int] = [0]
    var b: List[Int] = [2]
    for _ in range(4):
        a = apply_substitution(sigma, a)
        b = apply_substitution(sigma, b)
    assert_equal(a[3], 2)
    assert_equal(b[3], 2)
    assert_equal(parikh([a[0], a[1], a[2]]), [1, 0, 2])
    assert_equal(parikh([b[0], b[1], b[2]]), [1, 0, 2])

    var parent = Pair([0, 2, 2, 2, 0, 2, 2, 0, 1, 2],
                      [1, 2, 2, 0, 2, 2, 0, 2, 2, 0])
    var state = Pair([0, 1], [1, 0])
    for _ in range(5):
        var row = decompose(apply_substitution(sigma, state.u),
                            apply_substitution(sigma, state.v))
        state = normalise(row[0])
    assert_equal(state, parent)

    var bounded = build_bounded(sigma3(sigma), 64, 32)
    assert_true(bounded.complete())
    var comps = recurrent_noncoincident_sccs(bounded.graph)
    var found = False
    for i in range(len(comps)):
        for j in range(len(comps[i])):
            if bounded.graph.states[comps[i][j]] == parent:
                assert_equal(len(comps[i]), 1)
                var profile = profile_component(bounded.graph, comps[i])
                assert_false(profile.direct_coincidence)
                assert_true(profile.noncoincident_exit)
                found = True
    assert_true(found)

    var top = apply_substitution(sigma, parent.u)
    var bottom = apply_substitution(sigma, parent.v)
    var cuts = coincidence_boundaries(top, bottom)
    assert_equal(cuts, [0, 10, 17, 23])
    var row = decompose(top, bottom)
    assert_equal(len(row), 3)
    assert_equal(row[0], Pair(parent.v, parent.u))
    assert_equal(row[1], Pair([1, 2, 2, 0, 2, 2, 0], [2, 0, 2, 2, 0, 1, 2]))
    assert_equal(row[2], Pair([1, 0, 2, 2, 2, 0], [2, 0, 2, 2, 0, 1]))
    for i in range(len(row)):
        assert_equal(row[i].u[0], 1)
        assert_true(row[i].v[0] != 1)
        assert_false(row[i].is_coincidence())
    assert_equal(len(newborn_sync_positions(sigma, parent)), 0)
    for i in range(1, len(cuts) - 1):
        var cut = cuts[i]
        var birth = classify_irreducible_birth(sigma, parent, cut)
        assert_equal([birth.top_source, birth.top_digit], [3 * i + 1, 0])
        assert_equal([birth.bottom_source, birth.bottom_digit], [3 * i + 1, 1])
        assert_equal([top[cut - 1], bottom[cut - 1]], [0, 2])
        assert_equal([top[cut], bottom[cut]], [1, 2])

    var p = parikh(row[0].u)
    var q = parikh(row[1].u)
    var r = parikh(row[2].u)
    assert_equal(p, parikh(parent.u))
    assert_equal(_rank_det(p, q, r), -1)
    var e: List[Int] = [q[0] + r[0], q[1] + r[1], q[2] + r[2]]
    assert_equal(e, [4, 2, 7])
    assert_equal(m.apply(p), [p[0] + e[0], p[1] + e[1], p[2] + e[2]])
    assert_equal(_rank_det(p, e, m.apply(e)), -1)
    var cone = literal_two_generation_parikh_rank(sigma, parent)
    assert_equal(cone.rank, 3)
    assert_equal(cone.independent_ids, [0, 2, 3])

    var exit_row = decompose(apply_substitution(sigma, row[2].u),
                             apply_substitution(sigma, row[2].v))
    assert_equal(exit_row[1], Pair([2], [2]))
    var refused = False
    try:
        _ = audit_complete_strict_cones(sigma, [parent.copy()])
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_recurrent_flat_row_with_two_exits()
    print("C4 recurrent flat exits: 3 ordered children, phase 1, determinant -1, diagonal at [2,1].")
    require_contract("complete recurrent flat PIP child row with actual good-edge witness, every newborn address and both nonsync tests, exact exiting Parikh mass, and fail-closed strict audit")
