"""Independent whole-slice and unbounded guard checks; no BH promotion."""
from pathlib import Path
import runpy

import pytest

ROOT = Path(__file__).resolve().parents[1]
O = runpy.run_path(str(ROOT / "oracles/python/class_a_zero_defect_escape.py"))
S = runpy.run_path(str(ROOT / "oracles/python/class_a_zero_defect_symbolic.py"))


def test_entire_named_strict_slices_and_original_addresses():
    result = O["certify_fixtures"]()
    assert result["members"] == 14
    assert result["maximum_path_length"] == 10
    assert result["countercontrol"]["first_target_depth"] == 3
    assert not result["universal_seed_entry"]


def test_symbolic_chambers_prove_all_guards_and_zero_endpoints():
    result = S["certify"]()
    assert result["strict_zero_defect_length_bound"] == 10
    assert result["endpoint_chamber_paths"] == 199
    assert result["wrong_ordinal_control_rejected"]
    assert not result["universal_seed_entry"]


def test_false_domains_and_outside_slice_refuse():
    for k, t in ((0, 2), (1, 3), (4, 5)):
        assert not O["xx5_strict_domain"](k, t)
        with pytest.raises(ValueError):
            O["endpoint_addresses"](k, t, 0, 0, 5)
    for w in ((0, 0, 1, 0, -1), (2, 2, 0, 1, 0)):
        with pytest.raises(ValueError):
            O["zero_defect_addresses"](0, 0, w)
    with pytest.raises(ValueError):
        O["parameters"](-1, 0)
    with pytest.raises(ValueError):
        O["endpoint_addresses"](0, 0, 1, 1, 3)


def test_literal_bad_ordinal_and_changed_offset_are_rejected():
    g = O["Geometry"](-1, 0, 0)
    with pytest.raises(ValueError):
        O["literal_child"](g, (2, 2, 0, -4, 4), 4, 0)
    with pytest.raises(ValueError):
        O["replay"](g, (0, 0, -1, 0, 1), [(0, 7), (2, 1)])


def test_native_log_rejects_truncation_even_with_all_fourteen_members(tmp_path):
    log = tmp_path / "truncated-native.log"
    log.write_text("".join(f"ZERO_DEFECT_PATH {k} {t} 0 0 0 0 0 0\n"
                           for k, t in O["FIXTURES"]))
    with pytest.raises(ValueError, match="source coverage mismatch"):
        O["check_native_log"](log)


def test_native_log_rejects_duplicate_source_records(tmp_path):
    log = tmp_path / "duplicate-native.log"
    log.write_text("ZERO_DEFECT_PATH 0 0 0 0 0 0 0 0\n" * 2)
    with pytest.raises(ValueError, match="duplicate native source"):
        O["check_native_log"](log)
