"""Actual native output and adversarial complete-occurrence transcript checks."""
from pathlib import Path
import os
import runpy
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
V = runpy.run_path(str(ROOT / "oracles/python/class_a_plus_upper_recurrence.py"))


@pytest.fixture(scope="module")
def complete():
    path = Path(os.environ.get("PSC_UPPER_CENTRAL_NATIVE", str(ROOT /
        "evidence/class-a-plus-upper-recurrence-2026-11-15/native-attempt-2.log")))
    assert path.is_file(), "an actual canonical native transcript is required"
    contents = path.read_bytes().decode("utf-8")
    result = V["verify_transcript"](contents)
    assert result["paths"] == 818
    return contents


def test_actual_native_complete_grid_and_exact_large_prefixes(complete):
    result = V["verify_transcript"](complete)
    assert result["edges"] == 4728
    assert result["central_edges"] == 1806
    assert result["maximum_depth"] == 93
    assert result["maximum_central_depth"] == 62
    assert result["maximum_prefix_digits"] == 144
    assert result["native_controls"] == 28
    assert result["complete_original_prefixes"] and result["recurrence_executed"]
    assert not result["all_source_entry"] and not result["universal_BH"]


@pytest.mark.parametrize("column", [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])
def test_every_header_and_first_child_coordinate_is_bound(complete, column):
    tokens = complete.split("\n", 1)[0].split(" ")
    tokens[column] = str(int(tokens[column])+1)
    with pytest.raises(ValueError):
        V["parse_row"](" ".join(tokens))


@pytest.mark.parametrize("coordinate", range(6))
def test_each_complete_original_prefix_coordinate_is_bound(complete, coordinate):
    tokens = complete.split("\n", 1)[0].split(" ")
    tokens[len(tokens)-6+coordinate] = str(int(tokens[len(tokens)-6+coordinate])+1)
    with pytest.raises(ValueError, match="original prefixes"):
        V["parse_row"](" ".join(tokens))


def find_row(complete, key):
    prefix = "PLUS_UPPER_CENTRAL_PATH " + " ".join(map(str, key)) + " "
    return next(line for line in complete.split("\n") if line.startswith(prefix))


def test_scalar_constant_tail_does_not_erase_packet_reconstruction_delay(complete):
    row = find_row(complete, (7, 1, 1, 2, -5))
    _, record = V["parse_row"](row)
    assert record["central_depth"] == 1
    assert tuple(record["steps"][0]["target"]) == (2, 2, -1, -3, 6)
    tokens = row.split(" ")
    tokens[6] = "0"
    with pytest.raises(ValueError, match="cutoff"):
        V["parse_row"](" ".join(tokens))


def test_nonzero_selector_cycle_needs_an_actual_exit(complete):
    row = find_row(complete, (7, 1, 1, 3, -6))
    _, record = V["parse_row"](row)
    assert record["central_depth"] == 0 and record["result"]["depth"] == 3
    tokens = row.split(" ")
    tokens[6] = "1"
    with pytest.raises(ValueError, match="first cycle"):
        V["parse_row"](" ".join(tokens))


def test_negating_source_alone_is_not_track_reversal(complete):
    tokens = complete.split("\n", 1)[0].split(" ")
    for column in (3, 4, 5):
        tokens[column] = str(-int(tokens[column]))
    with pytest.raises(ValueError):
        V["parse_row"](" ".join(tokens))


def test_empty_zero_is_bound_to_zero_prefixes_and_full_zero(complete):
    row = find_row(complete, (7, 1, 0, 0, 0))
    _, record = V["parse_row"](row)
    assert record["result"]["depth"] == 0
    assert record["result"]["P"] == record["result"]["Q"] == (0, 0, 0)
    tokens = row.split(" ")
    tokens[-1] = "1"
    with pytest.raises(ValueError, match="original prefixes"):
        V["parse_row"](" ".join(tokens))


@pytest.mark.parametrize("kind", [
    "missing_source", "duplicate_source", "missing_total", "missing_contract",
    "duplicate_total", "wrong_path_count", "wrong_edge_count", "wrong_control_count",
    "no_final_lf", "carriage_return", "nul", "blank_line", "garbage", "short_row",
    "long_row", "leading_space", "trailing_space", "noncanonical_integer",
    "negative_index", "past_last_index", "false_typed_zero", "past_step_cap",
])
def test_complete_grid_and_receipt_refusals(complete, kind):
    rows = complete[:-1].split("\n")
    tokens = rows[0].split(" ")
    if kind == "missing_source": rows.pop(0)
    elif kind == "duplicate_source": rows[0] = rows[1]
    elif kind == "missing_total": rows.pop(-2)
    elif kind == "missing_contract": rows.pop()
    elif kind == "duplicate_total": rows.insert(-1, rows[-2])
    elif kind == "wrong_path_count": rows[-2] = rows[-2].replace("paths=818", "paths=817")
    elif kind == "wrong_edge_count": rows[-2] = rows[-2].replace("edges=4728", "edges=4727")
    elif kind == "wrong_control_count": rows[-2] = rows[-2].replace("controls=28", "controls=27")
    elif kind == "blank_line": rows.insert(0, "")
    elif kind == "garbage": rows.append("success")
    elif kind == "short_row": rows[0] = " ".join(tokens[:-1])
    elif kind == "long_row": rows[0] += " 0"
    elif kind == "leading_space": rows[0] = " " + rows[0]
    elif kind == "trailing_space": rows[0] += " "
    elif kind == "noncanonical_integer": tokens[1] = "07"
    elif kind == "negative_index": tokens[9] = "-1"
    elif kind == "past_last_index": tokens[10] = "10"
    elif kind == "false_typed_zero": tokens[13:16] = ["0", "0", "0"]
    elif kind == "past_step_cap": tokens[7] = "257"
    if kind in {"noncanonical_integer", "negative_index", "past_last_index", "false_typed_zero", "past_step_cap"}:
        rows[0] = " ".join(tokens)
    text = "\n".join(rows) + "\n"
    if kind == "no_final_lf": text = text[:-1]
    elif kind == "carriage_return": text = text.replace("\n", "\r\n", 1)
    elif kind == "nul": text = text.replace("\n", "\x00\n", 1)
    with pytest.raises(ValueError):
        V["verify_transcript"](text)


@pytest.mark.parametrize("separator", ["\r\n", "\r", "\u2028", "\v"])
def test_cli_preserves_raw_record_boundaries(complete, separator, tmp_path):
    path = tmp_path / "bad.log"
    path.write_bytes(complete.replace("\n", separator, 1).encode("utf-8"))
    result = subprocess.run([sys.executable, str(ROOT /
        "oracles/python/class_a_plus_upper_recurrence.py"), "--native", str(path)],
        capture_output=True, text=True, timeout=90)
    assert result.returncode != 0
    assert "accepted_finite_native_central_replay" not in result.stdout


def test_resource_limit_has_no_acceptance():
    with pytest.raises(ValueError, match="resource cap"):
        V["verify_transcript"]("x" * (V["MAX_BYTES"]+1))
