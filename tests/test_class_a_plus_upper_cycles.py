"""Actual native acceptance plus deliberately malformed literal transcripts."""
from pathlib import Path
import os
import runpy
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
V = runpy.run_path(str(ROOT / "oracles/python/class_a_plus_upper_cycles.py"))
O = V["O"]


@pytest.fixture(scope="module")
def complete():
    rows = []
    for n in V["N_VALUES"]:
        for J, H in O["CASES"]:
            member = O["LiteralMember"](n, J)
            for flip in (False, True):
                record = O["emit"](member, H, flip)
                result = O["replay"](member, record)
                values = [n, J, H, int(flip), *record["source"], result["depth"]]
                for step in record["steps"]:
                    values += [*step["indices"], *step["target"]]
                values += [*result["P"], *result["Q"]]
                rows.append("PLUS_UPPER_PATH " + " ".join(map(str, values)))
    text = "\n".join(rows + [V["TOTAL"], V["CONTRACT"]]) + "\n"
    # A successful complete baseline is mandatory before rejection tests.
    assert V["verify_transcript"](text)["paths"] == 160
    return text


def test_actual_canonical_native_transcript():
    path = Path(os.environ.get("PSC_UPPER_NATIVE", str(ROOT /
        "evidence/class-a-plus-upper-cycles-2026-11-15/native-final.log")))
    assert path.is_file(), "actual native transcript is required, not an optional skip"
    result = V["verify_transcript"](path.read_bytes().decode("utf-8"))
    assert result["paths"] == 160
    assert result["edges"] == 600
    assert result["maximum_depth"] == 7
    assert result["native_controls"] == 23
    assert result["complete_original_prefixes"]
    assert not result["recurrence_executed"]
    assert not result["all_source_entry"]
    assert not result["universal_BH"]


def test_complete_independent_control_baseline(complete):
    assert V["verify_transcript"](complete)["edges"] == 600


@pytest.mark.parametrize("column", [5, 6, 7, 8, 9, 13, 14, 15, 16, 17])
def test_every_full_source_and_first_target_field_is_bound(complete, column):
    rows = complete.splitlines()
    tokens = rows[0].split(" ")
    tokens[column] = str(int(tokens[column]) + 1)
    rows[0] = " ".join(tokens)
    with pytest.raises(ValueError):
        V["verify_transcript"]("\n".join(rows) + "\n")


@pytest.mark.parametrize("column", range(6))
def test_every_native_original_prefix_coordinate_is_bound(complete, column):
    rows = complete.splitlines()
    tokens = rows[0].split(" ")
    offset = len(tokens) - 6 + column
    tokens[offset] = str(int(tokens[offset]) + 1)
    rows[0] = " ".join(tokens)
    with pytest.raises(ValueError, match="prefix witnesses"):
        V["verify_transcript"]("\n".join(rows) + "\n")


@pytest.mark.parametrize("kind", [
    "missing_source", "duplicate_source", "missing_total", "missing_contract",
    "duplicate_total", "duplicate_contract", "wrong_count", "wrong_controls",
    "path_leading_space", "path_trailing_space", "total_leading_space",
    "contract_leading_space", "contract_tab", "blank_line", "no_final_lf",
    "carriage_return", "garbage", "short_row", "long_row", "short_depth",
    "wrong_orientation", "noncanonical_integer", "bad_integer", "negative_index",
    "past_last_index", "wrong_legal_index", "wrong_n", "wrong_J", "wrong_H",
])
def test_complete_receipt_and_literal_mutation_controls(complete, kind):
    rows = complete.splitlines()
    tokens = rows[0].split(" ")
    if kind == "missing_source": rows.pop(0)
    elif kind == "duplicate_source": rows[0] = rows[1]
    elif kind == "missing_total": rows.pop(-2)
    elif kind == "missing_contract": rows.pop()
    elif kind == "duplicate_total": rows.insert(-1, rows[-2])
    elif kind == "duplicate_contract": rows.append(rows[-1])
    elif kind == "wrong_count": rows[-2] = rows[-2].replace("160", "159")
    elif kind == "wrong_controls": rows[-2] = rows[-2].replace("23", "22")
    elif kind == "path_leading_space": rows[0] = " " + rows[0]
    elif kind == "path_trailing_space": rows[0] += " "
    elif kind == "total_leading_space": rows[-2] = " " + rows[-2]
    elif kind == "contract_leading_space": rows[-1] = " " + rows[-1]
    elif kind == "contract_tab": rows[-1] = rows[-1].replace(": ", ":\t")
    elif kind == "blank_line": rows.insert(0, "")
    elif kind == "garbage": rows.append("unverified success")
    elif kind == "short_row": rows[0] = " ".join(tokens[:-1])
    elif kind == "long_row": rows[0] += " 0"
    elif kind == "short_depth": tokens[10] = "2"
    elif kind == "wrong_orientation": tokens[4] = "2"
    elif kind == "noncanonical_integer": tokens[1] = "07"
    elif kind == "bad_integer": tokens[1] = "7.0"
    elif kind == "negative_index": tokens[11] = "-1"
    elif kind == "past_last_index": tokens[12] = "10"
    elif kind == "wrong_legal_index": tokens[12] = "1"
    elif kind == "wrong_n": tokens[1] = "6"
    elif kind == "wrong_J": tokens[2] = "5"
    elif kind == "wrong_H": tokens[3] = "5"
    if kind in {"short_depth", "wrong_orientation", "noncanonical_integer", "bad_integer",
                "negative_index", "past_last_index", "wrong_legal_index", "wrong_n",
                "wrong_J", "wrong_H"}:
        rows[0] = " ".join(tokens)
    text = "\n".join(rows) + "\n"
    if kind == "no_final_lf": text = text[:-1]
    if kind == "carriage_return": text = text.replace("\n", "\r\n")
    with pytest.raises(ValueError):
        V["verify_transcript"](text)


def test_native_parser_resource_exhaustion_refuses():
    with pytest.raises(ValueError, match="resource cap"):
        V["verify_transcript"]("x" * (V["MAX_BYTES"] + 1))


@pytest.mark.parametrize("separator", ["\r\n", "\r", "\u2028", "\v"])
def test_actual_cli_preserves_raw_record_separators(complete, separator, tmp_path):
    path = tmp_path / "altered.log"
    path.write_bytes(complete.replace("\n", separator, 1).encode("utf-8"))
    result = subprocess.run([sys.executable, str(ROOT /
        "oracles/python/class_a_plus_upper_cycles.py"), "--native", str(path)],
        capture_output=True, text=True)
    assert result.returncode != 0
    assert "accepted_finite_native_replay" not in result.stdout


def test_retired_JH4_path_has_actual_last_c():
    for J, H in ((1, 4), (2, 2), (4, 1)):
        member = O["LiteralMember"](7, J)
        source = O["source_packet"](J, H, False)
        first, _, _ = member.step(source, (1, 4))
        second, _, _ = member.step(first, (1, 9))
        assert second == (2, 1, H - 1, 3 * H - 1, 4 - 6 * H)
        assert member.strict(second)
