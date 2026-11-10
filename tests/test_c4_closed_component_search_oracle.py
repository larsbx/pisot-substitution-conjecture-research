"""Independent oracle for the K_2 = 0 window search off the PIP corpus
(docs/c4-closed-component-search-2026-11-07.md).

The canonical search is kernel/c4_closed_component_search.mojo
(kernel/psc/closed_component_search.mojo), pinned by
kernel/tests/test_c4_closed_component_search.mojo. This test runs the stdlib
oracle oracles/python/c4_closed_component_search.py, which shares no code with
it, and checks it against figures printed by the Mojo driver: the partition of
the gate's table, the per-length sizes of P_L (experiment A), the fixed-point
controls, a stride-97 slice of the window at L = 11, and individual specimens
with first-pass survivors at L = 11.
"""
import runpy
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
ORACLE = runpy.run_path(str(ROOT / "oracles/python/c4_closed_component_search.py"))
OracleFailure = ORACLE["OracleFailure"]

# `mojo run -I . c4_closed_component_search.mojo 11 20000 0 28764 97` (Mojo totals)
SLICE_97 = {
    "one-outside": {"specimens": 20, "first_pass_specimens": 1, "first_pass": 1, "nonempty": 0},
    "both-outside": {"specimens": 12, "first_pass_specimens": 1, "first_pass": 2, "nonempty": 0},
    "reducible": {"specimens": 118, "first_pass_specimens": 0, "first_pass": 0, "nonempty": 0},
}
ROWS_97 = [
    {"sigma": "1/2/001", "class": "both-outside", "first_pass": 2, "rounds": 1, "survivors": 0},
    {"sigma": "01/20/1", "class": "one-outside", "first_pass": 1, "rounds": 1, "survivors": 0},
]
# WINDOW_SPECIMEN lines of the full L = 11 run (sigma: first_pass, rounds, survivors)
ROWS_11 = {
    "12/0/20": (1, 1, 0),
    "112/0/1": (2, 1, 0),
    "101/2/0": (4, 1, 0),
    "221/2/0": (2, 1, 0),
    "21/02/1": (1, 1, 0),
}


def sigma_of(key):
    return tuple(tuple(int(ch) for ch in w) for w in key.split("/"))


@pytest.fixture(scope="module")
def p11():
    pairs = ORACLE["k2_zero_pairs"](11)
    return pairs, {p: t for t, p in enumerate(pairs)}


def test_partition_matches_the_gate_table():
    assert ORACLE["domain"]() == {
        "PIP": [4554, 1542],
        "one-outside": [3216, 1704],
        "both-outside": [3960, 1812],
        "reducible": [21588, 10134],
    }


def test_universe_sizes_match_experiment_a():
    assert ORACLE["universe_counts"](11) == {7: 6, 8: 24, 9: 198, 10: 1230, 11: 7644}


def test_permutations_keep_everything(p11):
    pairs, index = p11
    for sigma in (((0,), (1,), (2,)), ((1,), (2,), (0,))):
        assert ORACLE["window"](sigma, pairs, index) == (len(pairs), 0, len(pairs))


def test_cyc3_survives_alone_and_breaks_when_cut():
    w = ((0, 1, 1, 2, 2, 0, 1), (1, 2, 0, 0, 1, 1, 2))
    t1 = ((1, 2, 2, 0, 0, 1, 2), (2, 0, 1, 1, 2, 2, 0))
    t2 = ((0, 1, 2, 2, 0, 0, 1), (2, 0, 0, 1, 1, 2, 0))
    cyc = ((1,), (2,), (0,))
    assert ORACLE["window"](cyc, [w, t1, t2]) == (3, 0, 3)
    assert ORACLE["window"](cyc, [w, t1]) == (1, 1, 0)


def test_ex_nonpisot_filter_off_and_on(p11):
    sigma = ((1,), (0, 1, 2), (1,))
    # the child closure of (01, 10), normalised, computed here
    red, inflate = ORACLE["red"], ORACLE["inflate"]
    todo, seen = [((0, 1), (1, 0))], set()
    while todo:
        p = todo.pop()
        if p in seen:
            continue
        seen.add(p)
        todo.extend(red(inflate(sigma, p[0]), inflate(sigma, p[1])))
    states = sorted(seen)
    assert all(u != v for u, v in states)
    assert ORACLE["window"](sigma, states) == (len(states), 0, len(states))
    pairs, index = p11
    assert not any(s in index for s in states)
    assert ORACLE["window"](sigma, pairs, index)[2] == 0


def test_rows_at_eleven(p11):
    pairs, index = p11
    for key, want in ROWS_11.items():
        assert ORACLE["window"](sigma_of(key), pairs, index) == want, key


def test_stride_slice_matches_mojo():
    out = ORACLE["run_window"](11, 0, 28764, 97)
    assert out["pairs"] == 9102
    assert out["totals"] == SLICE_97
    assert out["rows"] == ROWS_97

