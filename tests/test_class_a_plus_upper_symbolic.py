"""All-n literal-address certificates and independent prefix cross-checks."""
from copy import deepcopy
from pathlib import Path
import runpy

import pytest

O = runpy.run_path(str(Path(__file__).resolve().parents[1] /
                      "oracles/python/class_a_plus_upper_symbolic.py"))
N = O["N"]


@pytest.fixture(scope="module")
def packet():
    return O["certify"]()


def test_all_sixteen_directed_unbounded_paths(packet):
    assert packet["directed_paths"] == 16
    assert packet["checked_edges"] == 60
    assert packet["original_occurrences"] == 120
    assert packet["maximum_path_length"] == 7
    assert packet["finite_sampling_used"] is False
    assert len(packet["negative_controls"]) == 17
    assert all(packet["negative_controls"].values())
    assert all(row["full_original_prefix_identity"] for row in packet["paths"])
    assert all(row["terminal"] == [2, 2, "0", "0", "0"] for row in packet["paths"])
    assert not packet["strict_geometry_formalized_here"]
    assert not packet["recurrence_executed"]
    assert not packet["all_source_entry"]
    assert not packet["universal_BH"]


def test_complete_case_set_has_the_independent_expected_lengths(packet):
    expected = {(1, 1): 3, (1, 2): 3, (1, 3): 5, (1, 4): 7,
                (2, 1): 3, (2, 2): 5, (3, 1): 2, (4, 1): 2}
    assert {(row["J"], row["H"], row["reversed"]) for row in packet["paths"]} == {
        (J, H, flip) for J, H in expected for flip in (False, True)}
    assert all(row["depth"] == expected[row["J"], row["H"]] for row in packet["paths"])


def _assert_vector(actual, expected):
    for left, right in zip(actual, expected):
        O["zero"](O["sympify"](left)-right)


@pytest.mark.parametrize("height", [1, 2])
def test_J1_base_original_prefixes_match_closed_form(height):
    case = next(case for case in O["cases"]() if (case["J"], case["H"]) == (1, height))
    row = O["certify_path"](case)
    _assert_vector(row["final_top_prefix"], (3, 0, 3*N+11))
    _assert_vector(row["final_bottom_prefix"],
                   (3+(N+4)*height, (N+4)*height,
                    3*N+11+(N**2+5*N+6)*height))
    _assert_vector(row["scaled_original_source"],
                   (-(N+4)*height, -(N+4)*height, -(N**2+5*N+6)*height))


def test_J2_base_original_prefixes_match_closed_form():
    case = next(case for case in O["cases"]() if (case["J"], case["H"]) == (2, 1))
    row = O["certify_path"](case)
    _assert_vector(row["final_top_prefix"], (1, 0, 0))
    _assert_vector(row["final_bottom_prefix"], (2*N+8, 2*N+5, 2*N**2+10*N+16))
    _assert_vector(row["scaled_original_source"], (-2*N-7, -2*N-5, -2*N**2-10*N-16))


@pytest.mark.parametrize("J", [3, 4])
def test_two_edge_zero_prefixes_match_closed_form(J):
    case = next(case for case in O["cases"]() if (case["J"], case["H"]) == (J, 1))
    row = O["certify_path"](case)
    _assert_vector(row["final_top_prefix"], (1, 0, 3))
    _assert_vector(row["final_bottom_prefix"], (J, J-3, 3*N+12-J+(N+1)*(J-3)))


def test_genuine_reversal_exchanges_the_complete_original_prefixes(packet):
    rows = {(row["J"], row["H"], row["reversed"]): row for row in packet["paths"]}
    for J, H in O["CASES"]:
        forward, backward = rows[J, H, False], rows[J, H, True]
        _assert_vector(backward["final_top_prefix"],
                       tuple(O["sympify"](x) for x in forward["final_bottom_prefix"]))
        _assert_vector(backward["final_bottom_prefix"],
                       tuple(O["sympify"](x) for x in forward["final_top_prefix"]))
        _assert_vector(backward["scaled_original_source"],
                       tuple(-O["sympify"](x) for x in forward["scaled_original_source"]))
        for f_edge, r_edge in zip(forward["records"], backward["records"]):
            assert f_edge["top_occurrence"] == r_edge["bottom_occurrence"]
            assert f_edge["bottom_occurrence"] == r_edge["top_occurrence"]


def test_deferred_JH4_ordinal_remains_valid_last_c_not_run_y():
    letter, prefix, witness = O["occurrence"](4, 2, N+2)
    assert letter == 1
    assert witness["kind"] == "LAST"
    _assert_vector(prefix, (1, 0, N+1))
    case = deepcopy(O["cases"]()[-1])
    case["steps"] = [dict(indices=(1, 4), target=(2, 2, -1, -3, 5)),
                     dict(indices=(1, N+2), target=(2, 2, 0, 2, -2)),
                     dict(indices=(1, 3), target=(2, 2, 0, 0, 0))]
    with pytest.raises(ValueError, match="target type"):
        O["certify_path"](case)


@pytest.mark.parametrize("coordinate", [2, 3, 4])
def test_each_full_offset_coordinate_is_independently_bound(coordinate):
    case = O["cases"]()[0]
    target = list(case["steps"][0]["target"])
    target[coordinate] += 1
    case["steps"][0]["target"] = tuple(target)
    with pytest.raises(ValueError, match="integer-polynomial identity"):
        O["certify_path"](case)


def test_chamber_face_and_incomplete_coefficient_method_refuse():
    with pytest.raises(ValueError, match="nonnegative guard"):
        O["nonnegative"](N-8)
    # A valid nonnegative polynomial can require a different proof method.
    # This checker refuses it instead of inventing a universal sign result.
    with pytest.raises(ValueError, match="nonnegative guard"):
        O["nonnegative"]((N-8)**2)


def test_nonpolynomial_and_fractional_indices_are_not_integer_certificates():
    for expression in (1/N, O["Rational"](1, 2)):
        with pytest.raises(ValueError, match="integer polynomial"):
            O["occurrence"](3, 2, expression)


def test_missing_final_edge_cannot_pass_only_affine_prefix_checks():
    case = O["cases"]()[3]
    case["steps"].pop()
    with pytest.raises(ValueError, match="complete typed y/y zero"):
        O["certify_path"](case)
