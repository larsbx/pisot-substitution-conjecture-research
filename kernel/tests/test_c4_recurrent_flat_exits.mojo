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
from psc.words import Pair, k2, parikh
from substitution_dynamics.automaton import recurrent_noncoincident_sccs


def segment(word: List[Int], start: Int, stop: Int) -> List[Int]:
    var result = List[Int]()
    for i in range(start, stop):
        result.append(word[i])
    return result^


def check_collared_interval(
    sigma: List[List[Int]], seed: Pair, seed_depth: Int, radius: Int,
    positions: List[List[Int]], masses: List[List[Int]],
    diagonals: List[List[Int]], determinant: Int,
) raises:
    var top = seed.u.copy()
    var bottom = seed.v.copy()
    for _ in range(seed_depth):
        top = apply_substitution(sigma, top)
        bottom = apply_substitution(sigma, bottom)
    for level in range(3):
        var left = positions[level][0]
        var right = positions[level][1]
        assert_true(left >= radius and right + radius <= len(top) and left < right)
        var cuts = coincidence_boundaries(top, bottom)
        var left_found = False
        var right_found = False
        for i in range(len(cuts)):
            left_found = left_found or cuts[i] == left
            right_found = right_found or cuts[i] == right
        assert_true(left_found and right_found)
        assert_equal(segment(top, left - radius, left + radius),
                     segment(top, right - radius, right + radius))
        assert_equal(segment(bottom, left - radius, left + radius),
                     segment(bottom, right - radius, right + radius))
        var u = segment(top, left, right)
        var v = segment(bottom, left, right)
        assert_equal(parikh(u), masses[level])
        assert_equal(parikh(v), masses[level])
        var row = decompose(u, v)
        var actual_diagonals = List[Int]()
        for i in range(len(row)):
            if row[i].is_coincidence():
                actual_diagonals.append(i)
        assert_equal(actual_diagonals, diagonals[level])
        if level < 2:
            assert_equal(len(apply_substitution(sigma, segment(top, 0, left))),
                         positions[level + 1][0])
            assert_equal(len(apply_substitution(sigma, segment(bottom, 0, left))),
                         positions[level + 1][0])
            assert_equal(len(apply_substitution(sigma, segment(top, 0, right))),
                         positions[level + 1][1])
            assert_equal(len(apply_substitution(sigma, segment(bottom, 0, right))),
                         positions[level + 1][1])
            top = apply_substitution(sigma, top)
            bottom = apply_substitution(sigma, bottom)
    assert_equal(_rank_det(masses[0], masses[1], masses[2]), determinant)


def test_collared_cut_controls() raises:
    var parent = Pair([0, 2, 2, 2, 0, 2, 2, 0, 1, 2],
                      [1, 2, 2, 0, 2, 2, 0, 2, 2, 0])
    check_collared_interval(
        [[1], [0, 2], [2, 2, 0]], parent, 1, 1,
        [[10, 17], [23, 39], [52, 88]],
        [[2, 1, 4], [5, 2, 9], [11, 5, 20]], [[], [], [5, 7]], 1,
    )
    var top = apply_substitution([[1], [0, 2], [2, 2, 0]], parent.u)
    assert_false(segment(top, 8, 12) == segment(top, 15, 19))

    check_collared_interval(
        [[1, 0], [1, 0, 2], [2, 1, 1]], Pair([1, 0, 2], [2, 1, 0]), 2, 2,
        [[11, 19], [30, 52], [82, 142]],
        [[2, 4, 2], [6, 10, 6], [16, 28, 16]], [[], [], []], 0,
    )

    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var u: List[Int] = [1, 0]
    var v: List[Int] = [0, 1]
    for _ in range(2):
        u = apply_substitution(sigma, u)
        v = apply_substitution(sigma, v)
    assert_equal(coincidence_boundaries(u, v), [0, 7, 9])


def check_hub_prefix_area(pair: Pair, hub: Int, area: Int, crossing: Int) raises:
    assert_true(pair.u[0] == hub and pair.v[0] != hub)
    var discrepancy = 0
    var accumulated = 0
    var first_crossing = -1
    for i in range(pair.length()):
        accumulated += discrepancy
        discrepancy += Int(pair.u[i] == hub) - Int(pair.v[i] == hub)
        if discrepancy < 0 and first_crossing == -1:
            first_crossing = i
    assert_equal(discrepancy, 0)
    assert_equal(accumulated, area)
    assert_equal(first_crossing, crossing)
    var counts = k2(pair)
    var wedge_area = 0
    for letter in range(3):
        wedge_area += counts[3 * hub + letter]
    assert_equal(wedge_area, area)


def test_hub_prefix_crossing_controls() raises:
    # The strict reducible control has a genuine good edge 0/1 and hub 2.
    var reducible: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    assert_equal(reducible[0][0], reducible[1][0])
    check_hub_prefix_area(Pair([2, 1, 0], [1, 0, 2]), 2, 2, -1)
    check_hub_prefix_area(Pair([2, 1, 1, 1, 0], [1, 1, 1, 0, 2]), 2, 4, -1)
    check_hub_prefix_area(Pair([2, 1, 1, 1, 0, 2, 1, 0], [1, 0, 2, 1, 0, 2, 1, 1]), 2, 2, -1)
    check_hub_prefix_area(
        Pair([2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0],
             [1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1]), 2, 2, -1,
    )

    var exits: List[List[Int]] = [[1], [0, 2], [2, 2, 0]]
    var parent = Pair([1, 2, 2, 0, 2, 2, 0, 2, 2, 0],
                      [0, 2, 2, 2, 0, 2, 2, 0, 1, 2])
    check_hub_prefix_area(parent, 1, 8, -1)
    var exit_row = decompose(apply_substitution(exits, parent.u),
                             apply_substitution(exits, parent.v))
    var expected_areas: List[Int] = [8, 5, 5]
    assert_equal(len(exit_row), len(expected_areas))
    for i in range(len(exit_row)):
        check_hub_prefix_area(Pair(exit_row[i].v, exit_row[i].u), 1, expected_areas[i], -1)

    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var seed = Pair([1, 0], [0, 1])
    check_hub_prefix_area(seed, 1, 1, -1)
    var first = decompose(apply_substitution(sigma, seed.u), apply_substitution(sigma, seed.v))
    assert_equal(len(first), 1)
    check_hub_prefix_area(first[0], 1, 0, 2)
    var second = decompose(apply_substitution(sigma, first[0].u),
                           apply_substitution(sigma, first[0].v))
    assert_equal(len(second), 2)
    check_hub_prefix_area(second[0], 1, -3, 2)
    check_hub_prefix_area(second[1], 1, 1, -1)

    # Reconstruct the offset cancellation at that crossing, then verify
    # that it gives an actual diagonal in the full physical words.
    var top = first[0].u.copy()
    var bottom = first[0].v.copy()
    assert_equal([top[2], bottom[2]], [0, 1])
    var top_prefix = segment(top, 0, 2)
    var bottom_prefix = segment(bottom, 0, 2)
    var a = parikh(top_prefix)
    var b = parikh(bottom_prefix)
    var defect: List[Int] = [a[0] - b[0], a[1] - b[1], a[2] - b[2]]
    assert_equal(defect, [-1, 0, 1])
    var top_image: List[Int] = [top[2]]
    var bottom_image: List[Int] = [bottom[2]]
    var m = Mat3(substitution_incidence(sigma))
    for _ in range(3):
        top = apply_substitution(sigma, top)
        bottom = apply_substitution(sigma, bottom)
        top_prefix = apply_substitution(sigma, top_prefix)
        bottom_prefix = apply_substitution(sigma, bottom_prefix)
        top_image = apply_substitution(sigma, top_image)
        bottom_image = apply_substitution(sigma, bottom_image)
        defect = m.apply(defect)
    assert_equal(defect, [2, 3, 2])
    assert_equal(parikh(segment(bottom_image, 0, 7)), defect)
    assert_equal([top_image[0], bottom_image[7]], [0, 0])
    assert_equal([len(top_prefix), len(bottom_prefix) + 7], [28, 28])
    assert_equal(parikh(segment(top, 0, 28)), [7, 12, 9])
    assert_equal(parikh(segment(bottom, 0, 28)), [7, 12, 9])
    assert_equal([top[28], bottom[28]], [0, 0])


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
    test_collared_cut_controls()
    test_hub_prefix_crossing_controls()
    print("C4 recurrent flat exits: 3 ordered children, phase 1, determinant -1, diagonal at [2,1].")
    require_contract("complete recurrent flat PIP child row with actual good-edge witness, every newborn address and both nonsync tests, exact exiting Parikh mass, and fail-closed strict audit")
    require_contract("literal collared cut intervals with transported endpoint equality, exact cycle masses and diagonals, and reducible and productive controls")
    require_contract("hub prefix area equals degree-two word defect, exact axis crossing and actual offset-to-diagonal witness, with strict reducible and recurrent exit controls")
