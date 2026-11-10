"""Uniform C4 two-generation Parikh-rank interface, with bounded literal tests.

The logical proof uses irreducible characteristic polynomial; this test checks
actual ordered word occurrences and negative input/lower-rank controls only.
"""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_two_generation_rank import literal_two_generation_parikh_rank
from psc.bpa import apply_substitution, decompose, coincidence_boundaries, prefix_endpoint_map, suffix_endpoint_map
from psc.c4_cut_alignment import classify_irreducible_birth, _eventually_equal
from psc.words import Pair, parikh


def test_real_secondary_is_sharp_at_second_generation() raises:
    # Real-secondary PIP: no newborn at depth one for swap (01,10).
    # First genuine full-rank descendant triple appears only at depth two.
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var root = Pair([0, 1], [1, 0])
    var a = literal_two_generation_parikh_rank(sigma, root)
    assert_equal(a.rank, 3)
    assert_equal(len(a.occurrences), 6)
    assert_equal(a.independent_ids, [0, 1, 4])
    assert_equal(a.occurrences[0].depth, 0)
    assert_equal(a.occurrences[1].depth, 1)
    assert_equal(a.occurrences[1].first_ordinal, 0)
    assert_equal(a.occurrences[4].depth, 2)
    assert_equal(a.occurrences[4].first_ordinal, 0)
    assert_equal(a.occurrences[4].second_ordinal, 2)
    assert_equal(a.occurrences[0].counts, [1, 1, 0])
    assert_equal(a.occurrences[1].counts, [1, 1, 1])
    assert_equal(a.occurrences[4].counts, [1, 0, 0])
    # No independent triple is available in depths zero and one.
    assert_equal(len(a.occurrences[0].counts), 3)
    assert_equal(a.occurrences[2].depth, 2)


def test_tribonacci_can_be_full_rank_earlier() raises:
    var sigma: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var a = literal_two_generation_parikh_rank(sigma, Pair([0, 1], [1, 0]))
    assert_equal(a.rank, 3)
    assert_equal(a.independent_ids, [0, 1, 2])
    assert_equal(a.occurrences[0].counts, [1, 1, 0])
    assert_equal(a.occurrences[1].counts, [1, 0, 0])
    assert_equal(a.occurrences[2].counts, [1, 1, 1])


def test_fixed_row_escape_requires_diagonals_and_occurrence_mass() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var root = Pair([0, 1], [1, 0])
    var result = literal_two_generation_parikh_rank(sigma, root)
    # The same nonzero rational row (1,-1,0) is tested on every actual
    # occurrence. It vanishes at depths 0 and 1, then sees only 0/0 at
    # depth 2, first ordinal 0, second ordinal 2.
    var detected = List[Int]()
    for i in range(len(result.occurrences)):
        var value = result.occurrences[i].counts[0] - result.occurrences[i].counts[1]
        if result.occurrences[i].depth < 2:
            assert_equal(value, 0)
        if value != 0:
            detected.append(i)
    assert_equal(detected, [4])
    assert_equal(result.occurrences[4].depth, 2)
    assert_equal(result.occurrences[4].first_ordinal, 0)
    assert_equal(result.occurrences[4].second_ordinal, 2)
    assert_equal(result.occurrences[4].counts, [1, 0, 0])

    var whole = root.u.copy()
    var expected: List[List[Int]] = [[1, 1, 0], [1, 1, 1], [2, 1, 3]]
    for depth in range(3):
        var mass: List[Int] = [0, 0, 0]
        for i in range(len(result.occurrences)):
            if result.occurrences[i].depth == depth:
                for a in range(3):
                    mass[a] += result.occurrences[i].counts[a]
        assert_equal(mass, expected[depth])
        assert_equal(mass, parikh(whole))
        whole = apply_substitution(sigma, whole)

    var first = decompose(apply_substitution(sigma, root.u), apply_substitution(sigma, root.v))
    assert_equal(len(first), 1)
    var second = decompose(
        apply_substitution(sigma, first[0].u), apply_substitution(sigma, first[0].v),
    )
    assert_equal(len(second), 4)
    assert_equal(second[0], Pair([0, 2, 1], [1, 2, 0]))
    assert_equal(second[1], Pair([2], [2]))
    assert_equal(second[2], Pair([0], [0]))
    assert_equal(second[3], Pair([2], [2]))
    var without_diagonal_mass: List[Int] = [0, 0, 0]
    var distinct_mass: List[Int] = [0, 0, 0]
    var unique = List[Pair]()
    for i in range(len(second)):
        var counts = parikh(second[i].u)
        if not second[i].is_coincidence():
            assert_equal(counts[0] - counts[1], 0)
            for a in range(3):
                without_diagonal_mass[a] += counts[a]
        var repeated = False
        for j in range(len(unique)):
            if second[i] == unique[j]:
                repeated = True
        if not repeated:
            unique.append(second[i].copy())
            for a in range(3):
                distinct_mass[a] += counts[a]
    assert_equal(without_diagonal_mass, [1, 1, 1])
    assert_equal(distinct_mass, [2, 1, 2])
    assert_true(distinct_mass != expected[2])
    assert_true(without_diagonal_mass != expected[2])


def test_fullrank_primitive_but_reducible_strict_control_stays_rank_two() raises:
    # Non-PIP four-state strict SCC: M is full rank, but its reducible
    # cubic preserves the proper plane p0=p2.
    var sigma: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var a = literal_two_generation_parikh_rank(
        sigma, Pair([1, 0, 2], [2, 1, 0])
    )
    assert_equal(a.rank, 2)
    assert_equal(len(a.occurrences), 7)
    assert_equal(a.independent_ids, [0, 1])
    for i in range(len(a.occurrences)):
        assert_equal(a.occurrences[i].counts[0], a.occurrences[i].counts[2])
        # Fixed nonzero row (1,0,-1) witnesses the missing irreducibility
        # premise even though the incidence matrix itself has full rank.
        assert_equal(a.occurrences[i].counts[0] - a.occurrences[i].counts[2], 0)


def test_caps_and_unbalanced_inputs_fail_closed() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var rejected = False
    try:
        _ = literal_two_generation_parikh_rank(
            sigma, Pair([0, 1], [1, 0]), node_cap=5
        )
    except:
        rejected = True
    assert_true(rejected)

    # Empty source has zero mass and cannot supply a cyclic nonzero vector.
    # The canonical bounded certificate refuses it rather than emitting rank.
    rejected = False
    try:
        _ = literal_two_generation_parikh_rank(sigma, Pair([], []))
    except:
        rejected = True
    assert_true(rejected)
    rejected = False
    try:
        _ = literal_two_generation_parikh_rank(
            sigma, Pair([0, 1], [0, 0])
        )
    except:
        rejected = True
    assert_true(rejected)
    rejected = False
    try:
        _ = literal_two_generation_parikh_rank(
            sigma, Pair([0, 1], [1, 0]), node_cap=0
        )
    except:
        rejected = True
    assert_true(rejected)


def test_repeated_diagonal_parents_and_exact_cap() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var seed = Pair([0, 0], [0, 0])
    var result = literal_two_generation_parikh_rank(sigma, seed, node_cap=7)
    assert_equal(len(result.occurrences), 7)
    assert_equal(result.independent_ids, [0, 1, 4])
    for i in range(2):
        assert_equal(result.occurrences[i + 1].first_ordinal, i)
        assert_equal(result.occurrences[i + 1].counts, [0, 1, 0])
        for j in range(2):
            var index = 3 + 2 * i + j
            assert_equal(result.occurrences[index].depth, 2)
            assert_equal(result.occurrences[index].first_ordinal, i)
            assert_equal(result.occurrences[index].second_ordinal, j)
        assert_equal(result.occurrences[3 + 2 * i].counts, [1, 0, 0])
        assert_equal(result.occurrences[4 + 2 * i].counts, [0, 0, 1])
    # Coincident parents must continue to inflate for the descendant-mass
    # statement. The production BPA's terminal convention is not this list.
    var mass: List[Int] = [0, 0, 0]
    for i in range(len(result.occurrences)):
        if result.occurrences[i].depth == 2:
            for a in range(3):
                mass[a] += result.occurrences[i].counts[a]
    assert_equal(mass, [2, 0, 2])
    var rejected = False
    try:
        _ = literal_two_generation_parikh_rank(sigma, seed, node_cap=6)
    except:
        rejected = True
    assert_true(rejected)


def test_invalid_root_digits_are_rejected_before_counting() raises:
    var sigma: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    for digit in [-1, 3]:
        var rejected = False
        try:
            _ = literal_two_generation_parikh_rank(sigma, Pair([digit], [0]))
        except:
            rejected = True
        assert_true(rejected)
        rejected = False
        try:
            _ = literal_two_generation_parikh_rank(sigma, Pair([0], [digit]))
        except:
            rejected = True
        assert_true(rejected)



def test_real_pip_zero_phase_flat_depth_two_rank_three_needs_later_sync() raises:
    # Primitive irreducible unimodular Pisot: x^3-3x^2+2x-1,
    # discriminant -23, M^2 positive. Good prefix edge {0,2} is
    # ACTUALLY coincident, not just compatible with an endpoint mask.
    var sigma: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    var h = prefix_endpoint_map(sigma)
    var g = suffix_endpoint_map(sigma)
    assert_equal(h, [0, 1, 0])
    assert_equal(g, [1, 2, 1])
    assert_true(_eventually_equal(h, 0, 2))
    var root = Pair([1, 0], [0, 1])
    var first = decompose(
        apply_substitution(sigma, root.u), apply_substitution(sigma, root.v),
    )
    assert_equal(len(first), 1)
    assert_equal(first[0].u, [1, 2, 0, 1])
    assert_equal(first[0].v, [0, 1, 1, 2])
    var second = decompose(
        apply_substitution(sigma, first[0].u),
        apply_substitution(sigma, first[0].v),
    )
    assert_equal(len(second), 2)
    assert_equal(second[0].u, [1, 2, 0, 2, 1, 0, 1])
    assert_equal(second[0].v, [0, 1, 1, 2, 1, 2, 0])
    assert_equal(second[1].u, [1, 2])
    assert_equal(second[1].v, [2, 1])
    # Hub 1 remains physically TOP in ALL actual noncoincident
    # descendant words through depth two: complete residual [0],[0,0].
    assert_equal(root.u[0], 1)
    assert_true(root.v[0] != 1)
    assert_equal(first[0].u[0], 1)
    assert_true(first[0].v[0] != 1)
    for i in range(2):
        assert_equal(second[i].u[0], 1)
        assert_true(second[i].v[0] != 1)

    var rank = literal_two_generation_parikh_rank(sigma, root)
    assert_equal(rank.rank, 3)
    assert_equal(len(rank.occurrences), 4)
    assert_equal(rank.independent_ids, [0, 1, 2])
    assert_equal(rank.occurrences[0].counts, [1, 1, 0])
    assert_equal(rank.occurrences[1].counts, [1, 2, 1])
    assert_equal(rank.occurrences[2].counts, [2, 3, 2])
    assert_equal(rank.occurrences[3].counts, [0, 1, 1])

    var top = apply_substitution(sigma, first[0].u)
    var bottom = apply_substitution(sigma, first[0].v)
    assert_equal(coincidence_boundaries(top, bottom), [0, 7, 9])
    var birth = classify_irreducible_birth(sigma, first[0], 7)
    assert_equal(birth.top_source, 3)
    assert_equal(birth.bottom_source, 3)
    assert_equal(birth.top_digit, 0)
    assert_equal(birth.bottom_digit, 1)
    assert_equal(birth.source_defect, [0, -1, 1])
    assert_equal(birth.local_correction, [-1, 0, 0])
    assert_equal(top[6], 1)
    assert_equal(bottom[6], 0)
    assert_equal(top[7], 1)
    assert_equal(bottom[7], 2)
    assert_true(not _eventually_equal(g, top[6], bottom[6]))
    assert_true(not _eventually_equal(h, top[7], bottom[7]))

    # At depth three the flat physical hub pattern breaks at actual
    # child ordinal 1: the good edge 0/2 becomes a newborn right pair.
    var third = decompose(
        apply_substitution(sigma, second[0].u),
        apply_substitution(sigma, second[0].v),
    )
    assert_equal(len(third), 3)
    assert_equal(third[1].u, [0, 2, 1, 1, 2])
    assert_equal(third[1].v, [2, 1, 1, 2, 0])
    var top3 = apply_substitution(sigma, second[0].u)
    var bottom3 = apply_substitution(sigma, second[0].v)
    assert_equal(coincidence_boundaries(top3, bottom3), [0, 7, 12, 16])
    assert_equal(top3[7], 0)
    assert_equal(bottom3[7], 2)
    assert_true(_eventually_equal(h, top3[7], bottom3[7]))
    # Genuine productive exit at depth four, along ordinals 0,0,1,0.
    var fourth = decompose(
        apply_substitution(sigma, third[1].u),
        apply_substitution(sigma, third[1].v),
    )
    assert_equal(fourth[0].u, [0])
    assert_equal(fourth[0].v, [0])

def main() raises:
    test_real_secondary_is_sharp_at_second_generation()
    test_tribonacci_can_be_full_rank_earlier()
    test_fixed_row_escape_requires_diagonals_and_occurrence_mass()
    test_fullrank_primitive_but_reducible_strict_control_stays_rank_two()
    test_caps_and_unbalanced_inputs_fail_closed()
    test_repeated_diagonal_parents_and_exact_cap()
    test_invalid_root_digits_are_rejected_before_counting()
    test_real_pip_zero_phase_flat_depth_two_rank_three_needs_later_sync()
    print("C4 two-generation literal Parikh rank controls passed.")
    require_contract("irreducible ternary PIP has a literal rank-three Parikh triple within two complete generations; fixed-row depth-two escape retains diagonal and repeated occurrences with exact mass, empty source and reducible strict rank-two controls, productive Tribonacci early rank, PIP flat zero-phase depth-two nonsync countercontrol with depth-three good-edge birth and depth-four diagonal, and cap/refusal negative controls")
