"""Independent literal geometry, full prefixes and refusal controls."""
from copy import deepcopy
from pathlib import Path
import runpy

import pytest

ROOT = Path(__file__).resolve().parents[1]
O = runpy.run_path(str(ROOT / "oracles/python/class_a_minus_constant_entry.py"))


@pytest.mark.parametrize("n,d", O["MEMBERS"])
def test_actual_lower_chamber_density(n, d):
    g = O["Geometry"](n, d)
    result = O["one_level_density"](g)
    assert result["inequalities"] == 10
    assert [r["counts"] for r in result["rows"]] == [
        [2, 0, n+d], [1, 1, n], [1, 1, n-1]]
    assert g.sign(O["add"](O["scale"](g.lengths[2], 2),
                           O["scale"](g.lengths[0], -1))) > 0


def test_all_height_descent_and_original_prefix_equality():
    g = O["Geometry"](120, 5)
    for height in (1, 2, 12):
        source = (2, 2, height, -height, 0)
        path = O["cycle_escape"](g, height)
        assert len(path) == 3*height
        assert path[0] == (5*height+2, 1, (2, 2, height, -height, -1))
        assert path[1] == (1, 122-5*height, (2, 2, height-1, -height-1, 2))
        for H, index in zip(range(height, 0, -1), range(2, len(path), 3)):
            assert path[index][2] == (2, 2, H-1, -H+1, 0)
        certificate = O["original_prefix_certificate"](g, source, path, typed=True)
        assert certificate["scaled_source"] == [
            p-q for p, q in zip(certificate["top_prefix"], certificate["bottom_prefix"])]
        reversed_path = O["cycle_escape"](g, height, True)
        assert reversed_path == [(j, i, O["reverse"](w)) for i, j, w in path]
        O["original_prefix_certificate"](g, O["reverse"](source), reversed_path, typed=True)


def test_exact_height_boundary_and_nonzero_fixed_point():
    source = (2, 2, 2, -2, 0)
    below = O["Geometry"](19, 5)
    assert not O["central"](below, source)
    with pytest.raises(ValueError, match="central"):
        O["cycle_escape"](below, 2)
    boundary = O["Geometry"](20, 5)
    assert O["central"](boundary, source)
    nearest = O["nearest_run"](boundary, source)
    assert nearest[2] == source  # This actual nonzero fixed point is not a zero hit.
    escaped = O["central_escape"](boundary, source)
    assert escaped[0] != nearest and len(escaped) == 6
    assert escaped[-1][2] == (2, 2, 0, 0, 0)


def test_original_indices_full_offsets_and_first_zero_are_checked():
    g = O["Geometry"](20, 5)
    source = (2, 2, 1, -1, 0)
    path = O["cycle_escape"](g, 1)
    assert path[-1][:2] == (1, 3)
    wrong = deepcopy(path)
    i, j, child = wrong[0]
    wrong[0] = (i+1, j, child)
    with pytest.raises(ValueError, match="altered"):
        O["original_prefix_certificate"](g, source, wrong)
    wrong = deepcopy(path)
    wrong[1] = (*wrong[1][:2], (2, 2, 0, -1, 2))
    with pytest.raises(ValueError, match="altered"):
        O["original_prefix_certificate"](g, source, wrong)
    wrong = deepcopy(path)
    wrong[-1] = (1, len(g.words[2]), wrong[-1][2])
    with pytest.raises(ValueError, match="nonexistent"):
        O["original_prefix_certificate"](g, source, wrong)
    with pytest.raises(ValueError, match="earlier zero"):
        O["original_prefix_certificate"](g, source, path+[(1, 1, (2, 2, 0, 0, 0))])
    with pytest.raises(ValueError, match="missing full integral"):
        O["original_prefix_certificate"](g, source, path[:-1])


def test_entry_and_typed_terminal_policies():
    g = O["Geometry"](6, 5)
    source = (0, 1, 0, 0, 0)
    assert O["entry_escape"](g, source) == []
    path = O["entry_escape"](g, source, typed=True)
    assert path and path[-1][2][0] == path[-1][2][1]
    certificate = O["original_prefix_certificate"](g, source, path, typed=True)
    assert certificate["top_prefix"] == certificate["bottom_prefix"]
    with pytest.raises(ValueError, match="earlier zero"):
        O["original_prefix_certificate"](g, source, path)
    with pytest.raises(ValueError, match="typed coincidence"):
        O["original_prefix_certificate"](g, source, [], typed=True)


def test_arbitrary_formal_entry_and_resource_refusal():
    g = O["Geometry"](6, 5)
    source = (0, 0, -1, -5, 6)
    assert g.interior(source) and not O["central"](g, source)
    path = O["entry_escape"](g, source)
    assert path
    O["original_prefix_certificate"](g, source, path)
    for limits in (dict(state_cap=1), dict(pair_cap=1), dict(step_cap=0)):
        with pytest.raises(ValueError, match="cap"):
            O["entry_escape"](g, source, **limits)
    with pytest.raises(ValueError, match="domain"):
        O["central_escape"](g, source)
    for bad in ((3, 3, 0, 0, 0), (2, 2, 0.0, 0, 0), (2, 2, 0, 0, 2)):
        with pytest.raises(ValueError, match="domain"):
            O["entry_escape"](g, bad)
        with pytest.raises(ValueError, match="domain"):
            O["central_escape"](g, bad)
        with pytest.raises(ValueError, match="central y/y"):
            O["nearest_run"](g, bad)


def test_family_domains_are_separate():
    for n, d in ((5, 5), (6, 4), (6, 7), (6.0, 5), (True, 5)):
        with pytest.raises(ValueError, match="chamber"):
            O["Geometry"](n, d)
    upper = O["ParentGeometry"](-1, 0, 3)
    assert upper.n == 6 and upper.d == 11
    with pytest.raises(ValueError, match="chamber"):
        O["one_level_density"](upper)


def test_expected_native_sources_are_complete_and_distinct():
    geometries = {key: O["Geometry"](*key) for key in O["MEMBERS"]}
    keys = O["expected_native_keys"](geometries)
    assert len(keys) == 1830
    assert sum(row[0] == "MINUS_CENTRAL_PATH" for row in keys) == 945
    assert sum(row[0] == "MINUS_CONSTANT_PATH" for row in keys) == 156
    assert sum(row[0] == "MINUS_ENTRY_PATH" for row in keys) == 567
    assert sum(row[0] == "MINUS_TYPED_ENTRY_PATH" for row in keys) == 162


def test_native_receipt_truncation_duplication_and_unknown_output(tmp_path):
    path = tmp_path / "bad.log"
    path.write_text("MINUS_CENTRAL_PATH 6 5 2 2 0 0 0 0\n")
    with pytest.raises(ValueError, match="incomplete"):
        O["check_native_log"](path)
    path.write_text(path.read_text()*2)
    with pytest.raises(ValueError, match="duplicate"):
        O["check_native_log"](path)
    path.write_text("unexpected success\n")
    with pytest.raises(ValueError, match="unexpected"):
        O["check_native_log"](path)
