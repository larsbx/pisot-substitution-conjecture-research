"""Independent symbolic verification of the class-A carrier closure and descent tables."""
import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("class_a_carrier_closure", ROOT / "oracles/python/class_a_carrier_closure.py")
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_uniform_closure_for_every_n_at_least_eight():
    stats = oracle.verify_closure(oracle.carrier_rows(), 8)
    assert stats["seeds_real"] == 9 and stats["seeds_unreal"] == 3
    assert stats["clip_fallbacks"] == 0
    assert stats["covered"] == 3802 and stats["gap_geometry"] == 3334


def test_uniform_closure_holds_from_five_with_conservative_clips():
    stats = oracle.verify_closure(oracle.carrier_rows(), 5)
    assert stats["seeds_real"] == 9 and stats["clip_fallbacks"] > 0


def test_uniform_descent_bound():
    rows = oracle.carrier_rows()
    result = oracle.verify_descent(rows, oracle.pieces(), oracle.descents(), 8)
    assert result == dict(pieces=155, targets=8, descent_rows=221, bound_slope=2, bound_const=9)


def test_sign_decisions_fail_closed():
    from fractions import Fraction
    assert oracle.sign_on_interval([1, -3], Fraction(1, 5)) == 1
    with pytest.raises(ValueError):
        oracle.sign_on_interval([-1, 10], Fraction(1, 5))   # root at 1/10
    with pytest.raises(ValueError):
        oracle.sign_on_interval([-1, 5], Fraction(1, 5))    # vanishes at the bound


def test_closure_refuses_below_the_floor_and_with_a_missing_row():
    rows = oracle.carrier_rows()
    with pytest.raises(ValueError):
        oracle.verify_closure(rows, 4)
    with pytest.raises(ValueError):
        oracle.verify_closure(rows[:-1], 8)


@pytest.mark.parametrize("damage", ["raised", "negative", "missing", "label", "child", "target"])
def test_descent_refuses_damaged_tables(damage):
    rows = oracle.carrier_rows()
    P, D = oracle.pieces(), oracle.descents()
    if damage == "raised":
        c = D[0][8]
        P = P[:c] + [tuple(P[c][:7]) + (P[c][7] + 50,)] + P[c + 1:]
    elif damage == "negative":
        P = [tuple(P[0][:7]) + (P[0][7] - 100,)] + P[1:]
    elif damage == "missing":
        D = D[:-1]
    elif damage == "label":
        D = [tuple(D[0][:7]) + (D[0][7] + 1, D[0][8])] + D[1:]
    elif damage == "child":
        D = [tuple(D[0][:8]) + ((D[0][8] + 1) % len(P),)] + D[1:]
    else:
        target = next(i for i, p in enumerate(P) if oracle.is_target(rows[p[0]], p))
        D = D + [(target, P[target][1], P[target][2], P[target][3], P[target][4], 0, 0, 0, 0)]
    with pytest.raises(ValueError):
        oracle.verify_descent(rows, P, D, 8)


def test_tables_are_the_committed_generated_tables():
    data = ROOT / "evidence/class-a-carrier-closure-2026-10-22/descent-table.json"
    if not data.exists():
        pytest.skip("evidence packet not present")
    import json
    table = json.loads(data.read_text())
    assert [tuple([ri] + list(lo) + list(hi) + list(fit)) for ri, lo, hi, fit in table["pieces"]] == oracle.pieces()
    assert [tuple([pi] + list(lo) + list(hi) + list(ty) + [cpi]) for pi, lo, hi, ty, cpi in table["descent"]] == oracle.descents()
