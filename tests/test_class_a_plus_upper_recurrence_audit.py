"""Independent receipt mutation controls; a synthetic fixture is not Lean acceptance."""
import importlib.util
from pathlib import Path
import subprocess
import sys

import pytest

SPEC = importlib.util.spec_from_file_location(
    "upper_recurrence_audit", Path(__file__).parents[1] / "tools/check_class_a_plus_upper_recurrence_audit.py")
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)

VALID = """PSC_CLASS_A_PLUS_UPPER_RECURRENCE_MODULE\tPscVerif.ClassAPlusUpperRecurrence\t96\t80
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_DECLARATIONS\t1\t96\t80
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.family_coefficients
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.forward_integer_bound
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.eventual_constant_tail
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.eventual_alternating_tail
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.energy_periodic_constant
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.shear_bound
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.twist_recurrence
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.reconstruction_delay
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.central_coordinate_recurrence
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.central_gap_in_run
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.run_gap_digit_step
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.nonzero_upper_cycle_control
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_ENDPOINT\tPsc.ClassAPlusUpperRecurrence.half_tie_control
PSC_CLASS_A_PLUS_UPPER_RECURRENCE_AUDIT_COMPLETE\t13\t39
PSC_CLASS_A_PLUS_UPPER_COMPLETION_MODULE\tPscVerif.ClassAPlusUpperCycleCompletion\t20\t18
PSC_CLASS_A_PLUS_UPPER_COMPLETION_ENDPOINT\tPsc.ClassAPlusUpperCycleCompletion.decrement_path
PSC_CLASS_A_PLUS_UPPER_COMPLETION_ENDPOINT\tPsc.ClassAPlusUpperCycleCompletion.all_ordered_paths
PSC_CLASS_A_PLUS_UPPER_COMPLETION_ENDPOINT\tPsc.ClassAPlusUpperCycleCompletion.all_signed_ordered_paths
PSC_CLASS_A_PLUS_UPPER_COMPLETION_ENDPOINT\tPsc.ClassAPlusUpperCycleCompletion.all_traced_strict_prefixes
PSC_CLASS_A_PLUS_UPPER_COMPLETION_AUDIT_COMPLETE\t4\t12
"""


def test_complete_contract_baseline():
    assert CHECKER.check_log(VALID) == {
        "modules": 2, "declarations": 116, "theorems": 98,
        "endpoints": 17, "negative_controls": 51,
    }


@pytest.mark.parametrize("index", range(22))
def test_every_required_row_is_mandatory(index):
    rows = VALID.splitlines()
    del rows[index]
    with pytest.raises(ValueError):
        CHECKER.check_log("\n".join(rows) + "\n")


@pytest.mark.parametrize("index", [0, 1, 2, 9, 15, 16, 20, 21])
def test_duplicate_receipts_are_refused(index):
    rows = VALID.splitlines()
    rows.insert(index, rows[index])
    with pytest.raises(ValueError):
        CHECKER.check_log("\n".join(rows) + "\n")


@pytest.mark.parametrize("before,after", [
    ("\t96\t80", "\t95\t80"),
    ("\t20\t18", "\t20\t17"),
    ("\t1\t96\t80", "\t1\t96\t79"),
    ("\t13\t39", "\t13\t38"),
    ("\t4\t12", "\t4\t11"),
    ("\t96\t80", "\t096\t80"),
    ("\t20\t18", "\t0\t0"),
    ("\t20\t18", "\t20\t21"),
    ("PscVerif.ClassAPlusUpperRecurrence", "PscVerif.ForeignRecurrence"),
    ("all_traced_strict_prefixes", "untraced_prefixes"),
    ("forward_integer_bound", "eventual_constant_tail"),
    ("reconstruction_delay", "reconstruction_immediate"),
    ("_AUDIT_COMPLETE", "_AUDIT_PENDING"),
    ("PSC_CLASS_A_PLUS_UPPER_COMPLETION_MODULE", " PSC_CLASS_A_PLUS_UPPER_COMPLETION_MODULE"),
])
def test_altered_contract_is_refused(before, after):
    assert before in VALID
    with pytest.raises(ValueError):
        CHECKER.check_log(VALID.replace(before, after, 1))


@pytest.mark.parametrize("suffix", [
    "error: failed proof\n", "PSC_CLASS_A_PLUS_UPPER_UNKNOWN\t0\n",
    "\x00\n", "\r\n", "warning: PSC_CLASS_A_PLUS_UPPER_COMPLETION_AUDIT_COMPLETE\t4\t12\n",
])
def test_unexpected_output_is_refused(suffix):
    with pytest.raises(ValueError):
        CHECKER.check_log(VALID + suffix)


def test_order_and_completion_are_mandatory():
    rows = VALID.splitlines()
    rows[0], rows[16] = rows[16], rows[0]
    with pytest.raises(ValueError):
        CHECKER.check_log("\n".join(rows) + "\n")
    with pytest.raises(ValueError):
        CHECKER.check_log("")
    with pytest.raises(ValueError):
        CHECKER.check_log(VALID[:-2])


def test_empty_lf_lines_are_allowed_intentionally():
    assert CHECKER.check_log("\n" + VALID.replace("\n", "\n\n")) == CHECKER.check_log(VALID)


@pytest.mark.parametrize("separator", ["\v", "\f", "\x1c", "\x1d", "\x1e", "\x85", "\u2028", "\u2029"])
def test_only_lf_delimits_rows(separator):
    with pytest.raises(ValueError):
        CHECKER.check_log(VALID.replace("\n", separator, 1))


@pytest.mark.parametrize("transcript", [
    VALID.replace("\n", "\r\n"),
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
