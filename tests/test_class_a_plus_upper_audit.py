"""Independent synthetic receipt controls; a fixture is not a fresh Lean run."""
import importlib.util
from pathlib import Path
import subprocess
import sys

import pytest

SPEC = importlib.util.spec_from_file_location(
    "upper_audit", Path(__file__).parents[1] / "tools/check_class_a_plus_upper_audit.py")
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)

VALID = """PSC_CLASS_A_PLUS_UPPER_MODULE\tPscVerif.ClassAMinusPrefixAssembly\t81\t43
PSC_CLASS_A_PLUS_UPPER_MODULE\tPscVerif.ClassAPlusUpperCycles\t86\t71
PSC_CLASS_A_PLUS_UPPER_DECLARATIONS\t2\t167\t114
PSC_CLASS_A_PLUS_UPPER_ENDPOINT\tPsc.ClassAPlusUpperCycles.small_decrement
PSC_CLASS_A_PLUS_UPPER_ENDPOINT\tPsc.ClassAPlusUpperCycles.base_one_path
PSC_CLASS_A_PLUS_UPPER_ENDPOINT\tPsc.ClassAPlusUpperCycles.base_two_path
PSC_CLASS_A_PLUS_UPPER_ENDPOINT\tPsc.ClassAPlusUpperCycles.eight_ordered_paths
PSC_CLASS_A_PLUS_UPPER_ENDPOINT\tPsc.ClassAPlusUpperCycles.signed_ordered_paths
PSC_CLASS_A_PLUS_UPPER_ENDPOINT\tPsc.ClassAPlusUpperCycles.eight_traced_strict_prefixes
PSC_CLASS_A_PLUS_UPPER_ENDPOINT\tPsc.ClassAPlusUpperCycles.zero_typed
PSC_CLASS_A_PLUS_UPPER_ENDPOINT\tPsc.ClassAPlusUpperCycles.disputed_last_is_c
PSC_CLASS_A_PLUS_UPPER_AUDIT_COMPLETE\t8\t24
"""


def test_complete_contract_baseline():
    assert CHECKER.check_log(VALID) == {
        "modules": 2, "declarations": 167, "theorems": 114,
        "endpoints": 8, "negative_controls": 24,
    }


@pytest.mark.parametrize("index", range(12))
def test_every_required_row_is_mandatory(index):
    rows = VALID.splitlines()
    del rows[index]
    with pytest.raises(ValueError):
        CHECKER.check_log("\n".join(rows) + "\n")


@pytest.mark.parametrize("index", [0, 1, 2, 3, 8, 11])
def test_duplicate_receipts_are_refused(index):
    rows = VALID.splitlines()
    rows.insert(index, rows[index])
    with pytest.raises(ValueError):
        CHECKER.check_log("\n".join(rows) + "\n")


@pytest.mark.parametrize("before,after", [
    ("\t81\t43", "\t80\t43"),
    ("\t86\t71", "\t86\t70"),
    ("\t2\t167\t114", "\t2\t167\t113"),
    ("\t8\t24", "\t8\t23"),
    ("\t81\t43", "\t081\t43"),
    ("\t86\t71", "\t0\t0"),
    ("\t86\t71", "\t86\t87"),
    ("ClassAMinusPrefixAssembly", "ForeignPrefixAssembly"),
    ("eight_traced_strict_prefixes", "untraced_prefixes"),
    ("small_decrement", "base_one_path"),
    ("_AUDIT_COMPLETE", "_AUDIT_PENDING"),
    ("PSC_CLASS_A_PLUS_UPPER_MODULE", " PSC_CLASS_A_PLUS_UPPER_MODULE"),
])
def test_altered_contract_is_refused(before, after):
    assert before in VALID
    with pytest.raises(ValueError):
        CHECKER.check_log(VALID.replace(before, after, 1))


@pytest.mark.parametrize("suffix", [
    "error: failed proof\n", "PSC_CLASS_A_PLUS_UPPER_UNKNOWN\t0\n",
    "\x00\n", "\r\n", "warning: PSC_CLASS_A_PLUS_UPPER_AUDIT_COMPLETE\t8\t24\n",
])
def test_unexpected_output_is_refused(suffix):
    with pytest.raises(ValueError):
        CHECKER.check_log(VALID + suffix)


def test_order_and_completion_are_mandatory():
    rows = VALID.splitlines()
    rows[0], rows[1] = rows[1], rows[0]
    with pytest.raises(ValueError):
        CHECKER.check_log("\n".join(rows) + "\n")
    with pytest.raises(ValueError):
        CHECKER.check_log("")
    with pytest.raises(ValueError):
        CHECKER.check_log(VALID[:-2])


def test_cli_preserves_and_rejects_carriage_returns(tmp_path):
    transcript = tmp_path / "audit.log"
    transcript.write_bytes(VALID.replace("\n", "\r\n").encode("utf-8"))
    result = subprocess.run(
        [sys.executable, str(Path(CHECKER.__file__)), str(transcript)],
        capture_output=True, text=True, check=False,
    )
    assert result.returncode == 1
    assert not result.stdout
    assert "noncanonical control character" in result.stderr


def test_empty_lf_lines_are_allowed_intentionally():
    assert CHECKER.check_log("\n" + VALID.replace("\n", "\n\n")) == CHECKER.check_log(VALID)


@pytest.mark.parametrize("separator", ["\v", "\f", "\x1c", "\x1d", "\x1e", "\x85", "\u2028", "\u2029"])
def test_only_lf_delimits_rows(separator):
    with pytest.raises(ValueError):
        CHECKER.check_log(VALID.replace("\n", separator, 1))


@pytest.mark.parametrize("transcript", [
    VALID.replace("\n", "\u2028", 1),
    VALID.replace("\n", "\v", 1),
    VALID[:-1],
])
def test_cli_rejects_non_lf_boundaries_and_incomplete_last_line(tmp_path, transcript):
    path = tmp_path / "audit.log"
    path.write_bytes(transcript.encode("utf-8"))
    result = subprocess.run(
        [sys.executable, str(Path(CHECKER.__file__)), str(path)],
        capture_output=True, text=True, check=False,
    )
    assert result.returncode == 1
    assert not result.stdout


def test_final_lf_is_required():
    with pytest.raises(ValueError, match="must end with LF"):
        CHECKER.check_log(VALID[:-1])
