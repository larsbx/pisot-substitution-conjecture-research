from psc_research.multidegree_sieve import (
    candidate_families,
    dimension_from_multidegrees,
    expected_candidate_weights,
    is_forced_above_beta,
    mobius,
    multidegree_multiplicity,
    sorted_weights,
    witt_dimension,
)


def test_mobius_small_values():
    assert [mobius(n) for n in range(1, 11)] == [1, -1, -1, 0, -1, 1, -1, 0, 0, 1]


def test_multidegree_sum_recovers_witt_dimension_through_degree_ten():
    expected = {2: 3, 3: 8, 4: 18, 5: 48, 6: 116, 7: 312, 8: 810, 9: 2184, 10: 5880}
    for degree, dimension in expected.items():
        assert dimension_from_multidegrees(degree) == dimension
        assert witt_dimension(3, degree) == dimension


def test_known_multidegree_multiplicities():
    assert multidegree_multiplicity((1, 1, 0)) == 1
    assert multidegree_multiplicity((1, 1, 1)) == 2
    assert multidegree_multiplicity((2, 2, 0)) == 1
    assert multidegree_multiplicity((2, 1, 1)) == 3
    assert multidegree_multiplicity((2, 2, 1)) == 6
    assert multidegree_multiplicity((2, 2, 2)) == 14
    # One-generator Lie words vanish above degree one.
    assert multidegree_multiplicity((5, 0, 0)) == 0


def test_complex_pair_candidate_patterns_degrees_two_through_ten():
    expected = {
        2: ((1, 1, 0),),
        3: ((1, 1, 1),),
        4: ((2, 1, 1), (2, 2, 0)),
        5: ((2, 2, 1),),
        6: ((2, 2, 2),),
        7: ((3, 2, 2), (3, 3, 1)),
        8: ((3, 3, 2),),
        9: ((3, 3, 3),),
        10: ((4, 3, 3), (4, 4, 2)),
    }
    for degree, weights in expected.items():
        assert expected_candidate_weights(degree, complex_pair=True) == weights


def test_three_real_root_branch_removes_upper_repeated_boundary_family():
    expected = {
        2: ((1, 1, 0),),
        3: ((1, 1, 1),),
        4: ((2, 1, 1),),
        5: ((2, 2, 1),),
        6: ((2, 2, 2),),
        7: ((3, 2, 2),),
        8: ((3, 3, 2),),
        9: ((3, 3, 3),),
        10: ((4, 3, 3),),
    }
    for degree, weights in expected.items():
        assert expected_candidate_weights(degree, complex_pair=False) == weights


def test_every_omitted_positive_multidegree_is_forced_above_beta():
    for degree in range(2, 11):
        complex_candidates = set(expected_candidate_weights(degree, complex_pair=True))
        real_candidates = set(expected_candidate_weights(degree, complex_pair=False))
        for weight in sorted_weights(degree):
            assert is_forced_above_beta(weight, complex_pair=True) == (weight not in complex_candidates)
            assert is_forced_above_beta(weight, complex_pair=False) == (weight not in real_candidates)


def test_candidate_operator_types_follow_mod_three_pattern():
    assert [(f.label, f.operator_type) for f in candidate_families(6)] == [
        ("balanced_scalar", "det^m scalar"),
    ]
    assert [(f.label, f.operator_type) for f in candidate_families(7)] == [
        ("standard_twist", "det^m tensor V"),
        ("pair_square", "det^(m-1) times squared Lambda^2 orbit"),
    ]
    assert [(f.label, f.operator_type) for f in candidate_families(8)] == [
        ("dual_twist", "det^m tensor Lambda^2(V)"),
    ]
