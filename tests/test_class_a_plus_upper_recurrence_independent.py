"""Independent literal central paths, delayed reconstruction, and refusals."""
import copy
from pathlib import Path
import runpy

import pytest

ROOT = Path(__file__).resolve().parents[1]
O = runpy.run_path(str(ROOT / "oracles/python/class_a_plus_upper_recurrence_independent.py"))


@pytest.fixture(scope="module")
def large_baseline():
    member = O["LiteralMember"](31, 1)
    source = (2, 2, 100, -83, member.central_r(100, -83))
    record = O["emit"](member, source)
    result = O["replay"](member, record)
    assert source == (2, 2, 100, -83, -225)
    assert result["central_depth"] == 62 and result["depth"] == 93
    assert max(result["P"] + result["Q"]) > 2**63
    return member, record, result


def test_complete_independent_declared_source_grid():
    sources = O["source_grid"]()
    assert len(sources) == len(set(sources)) == 818
    paths = edges = central_edges = 0
    maximum_depth = maximum_central_depth = 0
    member = None
    for n, J, p, q, r in sources:
        if member is None or (member.n, member.J) != (n, J):
            member = O["LiteralMember"](n, J)
        record = O["emit"](member, (2, 2, p, q, r))
        result = O["replay"](member, record)
        paths += 1
        edges += result["depth"]
        central_edges += result["central_depth"]
        maximum_depth = max(maximum_depth, result["depth"])
        maximum_central_depth = max(maximum_central_depth, result["central_depth"])
    assert paths == 818 and edges > central_edges > 0
    assert (maximum_depth, maximum_central_depth) == (93, 62)


def test_full_packet_needs_one_more_step_than_constant_scalar_tail():
    member = O["LiteralMember"](7, 1)
    source = (2, 2, 1, 2, -5)
    assert member.central(source)
    assert O["cycle_height"](source) is None
    assert (source[2], -(2*source[2]+source[3]+source[4])) == (1, 1)
    record = O["emit"](member, source)
    result = O["replay"](member, record)
    assert record["steps"][0]["indices"] == (1, 1)
    assert record["steps"][0]["target"] == (2, 2, -1, -3, 6)
    assert result["central_depth"] == 1
    bad = copy.deepcopy(record)
    bad["central_depth"] = 0
    with pytest.raises(ValueError, match="full strictly central W"):
        O["replay"](member, bad)


def test_zero_source_has_bound_parameters_and_empty_prefixes():
    member = O["LiteralMember"](7, 14)
    record = O["emit"](member, (2, 2, 0, 0, 0))
    result = O["replay"](member, record)
    assert result == dict(P=(0, 0, 0), Q=(0, 0, 0), M_power_source=(0, 0, 0),
                          depth=0, central_depth=0, B=14)
    bad = copy.deepcopy(record)
    bad["J"] = 1
    with pytest.raises(ValueError, match="different upper parameters"):
        O["replay"](member, bad)


@pytest.mark.parametrize("coordinate", range(3))
def test_all_integral_target_coordinates_are_mandatory(large_baseline, coordinate):
    member, record, _ = large_baseline
    bad = copy.deepcopy(record)
    target = list(bad["steps"][0]["target"])
    target[coordinate+2] += 1
    bad["steps"][0]["target"] = target
    with pytest.raises(ValueError, match="complete integral offset"):
        O["replay"](member, bad)


@pytest.mark.parametrize("prefix", ("top_prefix", "bottom_prefix"))
@pytest.mark.parametrize("coordinate", range(3))
def test_all_original_prefix_coordinates_are_mandatory(large_baseline, prefix, coordinate):
    member, record, _ = large_baseline
    bad = copy.deepcopy(record)
    value = list(bad["steps"][0][prefix])
    value[coordinate] += 1
    bad["steps"][0][prefix] = value
    with pytest.raises(ValueError, match="original local occurrence prefix"):
        O["replay"](member, bad)


def test_negative_contract_controls_and_caps_have_successful_baselines():
    mutations, refusals = O["negative_controls"]()
    assert len(mutations) == 15
    assert set(refusals) == {"word_occurrences", "root_refinement", "path_steps"}


def test_equal_gap_at_different_legal_RUN_positions_is_not_the_selector():
    member = O["LiteralMember"](7, 1)
    source = (2, 2, 1, 2, -5)
    record = O["emit"](member, source)
    O["replay"](member, record)
    bad = copy.deepcopy(record)
    target, p, q = member.step(source, (2, 2))
    assert target == tuple(record["steps"][0]["target"])
    bad["steps"][0].update(indices=(2, 2), top_prefix=p, bottom_prefix=q)
    with pytest.raises(ValueError, match="wrong unique nearest original RUN"):
        O["replay"](member, bad)


@pytest.mark.parametrize("n,J", [(6, 1), (7, 0), (7, 15), (True, 1), (7, True)])
def test_outside_upper_domain_is_not_a_verdict(n, J):
    with pytest.raises(ValueError):
        O["LiteralMember"](n, J)


@pytest.mark.parametrize("J", (1, 2, 3, 4, 5, 14))
def test_family_split_rejects_global_absolute_contraction(J):
    member = O["LiteralMember"](7, J)
    # beta(beta+1)*(1-A-C)=(J-4)*beta-4.
    sign = member.sign_numerator((-4, J-4, 0))
    assert sign == (-1 if J <= 4 else 1)
    if J <= 4:
        # Twice beta(beta+1)*(C-1/2-2A)>0 authenticates the shear row.
        assert member.sign_numerator((-4, -3-2*J, 1)) == 1


def test_signed_sources_reverse_actual_indices_and_full_packets(large_baseline):
    member, positive, result = large_baseline
    negative = O["emit"](member, (2, 2, *(-x for x in positive["source"][2:])))
    reverse_result = O["replay"](member, negative)
    assert reverse_result["depth"] == result["depth"]
    assert reverse_result["central_depth"] == result["central_depth"]
    assert reverse_result["P"] == result["Q"]
    assert reverse_result["Q"] == result["P"]
    for first, second in zip(positive["steps"], negative["steps"]):
        assert tuple(second["indices"]) == tuple(first["indices"])[::-1]
        target = first["target"]
        assert tuple(second["target"]) == (target[1], target[0], *(-x for x in target[2:]))


def test_output_archive_is_preserved_on_refusal(tmp_path):
    existing = tmp_path / "summary.json"
    existing.write_text("historical record\n")
    with pytest.raises(ValueError, match="historical evidence preserved"):
        O["certify"](tmp_path)
    assert existing.read_text() == "historical record\n"
