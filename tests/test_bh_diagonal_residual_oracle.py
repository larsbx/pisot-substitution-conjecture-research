"""Independent oracle refusal controls for the finite residual certificates."""
from pathlib import Path
import runpy

import pytest

API = runpy.run_path(str(Path(__file__).parents[1] / "oracles/python/bh_diagonal_residual.py"))


@pytest.fixture(scope="module")
def certificate():
    edges, ranks, _, _ = API["graph"](12)
    return {u: (rank, next((v[1] for v in edges[u] if ranks[v] == rank-1), 0)
                if rank > 0 else 0) for u, rank in ranks.items()}


def test_exact_coefficients_and_full_finite_control(certificate):
    sign, _ = API["sign_function"](12)
    assert sign((-12, 1, 0)) == 1
    assert sign((-49, 4, 0)) == -1
    assert sign((0, 0, 0)) == 0
    receipt = API["check_parameter"](12, certificate)
    assert receipt["disk_pairs"] == 437
    assert receipt["uncovered_disk"] == 0
    assert receipt["uncovered_square"] > 0
    assert set(map(tuple, receipt["nonaxis_one_step_failures"])) == {
        (3, 4), (-3, -4), (6, -4), (-6, 4),
    }


def test_forged_rank_and_selected_digit_are_refused(certificate):
    pair = next(u for u, (rank, _) in certificate.items() if rank > 1)
    forged = dict(certificate)
    rank, selected = forged[pair]
    forged[pair] = rank+1, selected
    with pytest.raises(ValueError, match="rank mismatch"):
        API["check_parameter"](12, forged)
    forged[pair] = rank, 13
    with pytest.raises(ValueError, match="descending edge"):
        API["check_parameter"](12, forged)


def test_incomplete_coverage_is_refused(certificate):
    truncated = dict(certificate)
    truncated.pop((0, 0))
    with pytest.raises(ValueError, match="coverage"):
        API["check_parameter"](12, truncated)


def test_duplicate_export_and_outside_scope_are_refused(tmp_path):
    data = tmp_path / "duplicate.csv"
    data.write_text("r,z,y,rank,next_t\n12,0,0,0,0\n12,0,0,0,0\n")
    with pytest.raises(ValueError, match="duplicate"):
        API["read_native"](data)
    data.write_text("r,z,y,rank,next_t\n11,0,0,0,0\n")
    with pytest.raises(ValueError, match="outside"):
        API["read_native"](data)
    with pytest.raises(ValueError, match="parameter"):
        API["root_interval"](11)
