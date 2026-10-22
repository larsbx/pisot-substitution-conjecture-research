"""Independent symbolic verification of the class-A minus line (n+1,n,n-1) closure and descent."""
import importlib.util
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


def _load(line):
    """A fresh oracle module instance; the oracle selects its line from argv at import."""
    saved = sys.argv
    sys.argv = ["class_a_carrier_closure", "--line", line]
    try:
        spec = importlib.util.spec_from_file_location("class_a_carrier_closure_" + line, ROOT / "oracles/python/class_a_carrier_closure.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    finally:
        sys.argv = saved
    return module


oracle = _load("minus")
plus = _load("plus")


def test_line_data_rederived_from_the_incidence_matrix():
    oracle._check_line()
    assert oracle.EPS == -1 and oracle.RUN[2] == (1, -1)
    assert oracle.L_POLY == {0: [1, 3, 1], 1: [1, 2], 2: [1, 1]}


def test_uniform_closure_for_every_n_at_least_eight():
    stats = oracle.verify_closure(oracle.carrier_rows(), 8)
    assert stats["seeds_real"] == 9 and stats["seeds_unreal"] == 3
    assert stats["covered"] == 4508 and stats["gap_geometry"] == 3842
    assert stats["clip_fallbacks"] == 56


def test_uniform_closure_is_clip_free_from_ten():
    assert oracle.verify_closure(oracle.carrier_rows(), 10)["clip_fallbacks"] == 0


def test_uniform_descent_bound():
    rows = oracle.carrier_rows()
    result = oracle.verify_descent(rows, oracle.pieces(), oracle.descents(), 8)
    assert result == dict(pieces=176, targets=8, descent_rows=265, bound_slope=2, bound_const=11)


def test_refusals_below_the_floor_and_with_a_missing_row():
    rows = oracle.carrier_rows()
    with pytest.raises(ValueError):
        oracle.verify_closure(rows, 6)
    with pytest.raises(ValueError):
        oracle.verify_descent(rows, oracle.pieces(), oracle.descents(), 7)
    for drop in (0, 50, len(rows) - 1):
        with pytest.raises(ValueError):
            oracle.verify_closure(rows[:drop] + rows[drop + 1:], 8)


def test_a_carrier_is_bound_to_its_line():
    with pytest.raises(ValueError):
        plus.verify_closure(oracle.carrier_rows(), 8)
    with pytest.raises(ValueError):
        oracle.verify_closure(plus.carrier_rows(), 8)


@pytest.mark.parametrize("damage", ["raised", "missing", "label", "child"])
def test_descent_refuses_damaged_tables(damage):
    rows = oracle.carrier_rows()
    P, D = oracle.pieces(), oracle.descents()
    if damage == "raised":
        c = D[0][8]
        P = P[:c] + [tuple(P[c][:7]) + (P[c][7] + 50,)] + P[c + 1:]
    elif damage == "missing":
        D = D[1:]
    elif damage == "label":
        D = [tuple(D[0][:7]) + (D[0][7] + 1, D[0][8])] + D[1:]
    else:
        D = [tuple(D[0][:8]) + ((D[0][8] + 1) % len(P),)] + D[1:]
    with pytest.raises(ValueError):
        oracle.verify_descent(rows, P, D, 8)


def test_tables_are_the_committed_generated_tables():
    data = ROOT / "evidence/class-a-minus-line-2026-10-22/descent-table.json"
    if not data.exists():
        pytest.skip("evidence packet not present")
    table = json.loads(data.read_text())
    assert [tuple([ri] + list(lo) + list(hi) + list(fit)) for ri, lo, hi, fit in table["pieces"]] == oracle.pieces()
    assert [tuple([pi] + list(lo) + list(hi) + list(ty) + [cpi]) for pi, lo, hi, ty, cpi in table["descent"]] == oracle.descents()
