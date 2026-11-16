"""Unbounded-chamber proof checks and literal-address corruption controls."""
from copy import deepcopy
from pathlib import Path
import runpy

import pytest

ROOT = Path(__file__).resolve().parents[1]
S = runpy.run_path(str(ROOT / "oracles/python/class_a_central_entry_symbolic.py"))


def test_every_symbolic_cycle_chamber_and_density_margin():
    result = S["certify"]()
    assert result["small_KH_chambers"] == 6
    assert result["general_KH_chambers"] == 4
    assert result["directed_paths_including_reversal"] == 20
    assert result["checked_directed_edges"] == 58
    assert result["exact_reversed_QH_splices"] == 4
    assert result["small_cycle_zero_length_bound"] == 5
    assert result["density"]["strict_density_margin_certificates"] == 36
    assert all(result["controls"].values())
    assert not result["whole_theorem_formalized_in_Lean"]


def test_reversal_requires_swapping_original_occurrences():
    case = S["small_cases"]()[2]  # K=2,H=1 has asymmetric actual digits.
    with pytest.raises(ValueError):
        S["certify_path"](case["n"], case["K"], S["reverse"](case["source"]),
            case["addresses"], [S["reverse"](a) for a in case["expected"]],
            require_zero=True)


def test_suffix_splice_retains_the_exact_reversed_Q_packet():
    case = deepcopy(S["general_cases"]()[0])
    a, b, p, q, r = case["expected"][-1]
    case["expected"][-1] = (a, b, p, q+1, r-1)
    with pytest.raises(ValueError, match="coefficient identity"):
        S["certify_splice"](case)


def test_nonnegative_chamber_faces_do_not_supply_strict_positivity():
    u, z = S["u"], S["z"]
    with pytest.raises(ValueError, match="closed face"):
        S["positive_rational"](u*(1+z))
    accepted = S["positive_rational"]((1+u)*z/(1+z))
    assert accepted["coefficient_terms"] == 2


def test_guards_cannot_hide_an_undeclared_parameter():
    with pytest.raises(ValueError, match="outside its declared"):
        S["nonnegative"](S["K"]+1)
