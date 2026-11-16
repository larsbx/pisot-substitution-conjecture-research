"""Independent occurrence, prefix, source-coverage and terminal-policy controls."""
from copy import deepcopy
from pathlib import Path
import runpy

import pytest

ROOT = Path(__file__).resolve().parents[1]
O = runpy.run_path(str(ROOT / "oracles/python/class_a_central_entry.py"))


@pytest.mark.parametrize("k,t", O["MEMBERS"])
def test_literal_two_level_density(k, t):
    g = O["Geometry"](-1, k, t)
    rows = O["two_level_density"](g)
    assert len(rows) == 3
    n, A = g.n, g.n+g.d
    assert [r["counts"] for r in rows] == [
        [A+4, A, A*(n+1)],
        [n+3, n+1, A+n*n],
        [n+2, n, A+n*n-n+1],
    ]


def test_original_prefix_identity_and_terminal_policies():
    g = O["Geometry"](-1, 0, 3)
    source = (0, 1, 0, 0, 0)
    # This is already a BH half coincidence; it is not a typed coincidence.
    assert O["entry_escape"](g, source) == []
    path = O["entry_escape"](g, source, typed=True)
    assert path and path[-1][2][0] == path[-1][2][1]
    cert = O["original_prefix_certificate"](g, source, path, typed=True)
    assert cert["top_prefix"] == cert["bottom_prefix"]
    assert cert["top_ordinal"] == cert["bottom_ordinal"]
    assert cert["terminal_policy"] == "typed coincidence"
    with pytest.raises(ValueError, match="earlier zero"):
        O["original_prefix_certificate"](g, source, path)
    with pytest.raises(ValueError, match="typed coincidence"):
        O["original_prefix_certificate"](g, source, [], typed=True)
    for invalid in ((3, 3, 0, 0, 0), (2, 2, 0.0, 0, 0), (2, 2, 0, 0, 2)):
        with pytest.raises(ValueError, match="strict integral source"):
            O["original_prefix_certificate"](g, invalid, [], typed=True)


def test_genuine_last_boundary_and_changed_occurrence_refusal():
    g = O["Geometry"](-1, 0, 3)
    source = (2, 2, 3, 9, -18)
    path = O["cycle_escape"](g, 3)
    assert len(path) == 5
    assert path[3] == (1, 18, (2, 0, 0, 4, -4))
    cert = O["original_prefix_certificate"](g, source, path)
    assert cert["scaled_source"] == [p-q for p, q in zip(cert["top_prefix"], cert["bottom_prefix"])]
    bad = deepcopy(path)
    bad[3] = (1, 18, (2, 2, 0, 4, -4))
    with pytest.raises(ValueError, match="altered"):
        O["original_prefix_certificate"](g, source, bad)
    bad = deepcopy(path)
    bad[3] = (1, 19, path[3][2])
    with pytest.raises(ValueError, match="nonexistent"):
        O["original_prefix_certificate"](g, source, bad)
    reverse = O["reverse"](source)
    reversed_path = O["cycle_escape"](g, 3, True)
    assert reversed_path == [(j, i, O["reverse"](w)) for i, j, w in path]
    O["original_prefix_certificate"](g, reverse, reversed_path)
    # The adjacent n=7 parameter uses the same formula at a genuine RUN y.
    adjacent = O["Geometry"](-1, 0, 4)
    assert O["cycle_escape"](adjacent, 3)[3] == (1, 20, (2, 2, 0, 4, -4))


def test_nonzero_nearest_cycle_requires_an_alternative_child():
    g = O["Geometry"](-1, 0, 20)
    source = (2, 2, 8, 24, -48)
    first = O["nearest_run"](g, source)
    assert first[2] == O["reverse"](source)
    assert O["nearest_run"](g, first[2])[2] == source
    assert source[2:] != (0, 0, 0)
    path = O["central_escape"](g, source)
    assert path[0] != first
    assert path[-1][2][2:] == (0, 0, 0)


def test_arbitrary_formal_source_and_caps():
    g = O["Geometry"](-1, 0, 20)
    source = (2, 2, 10, -738, 738)
    assert g.interior(source)
    path = O["entry_escape"](g, source)
    assert path
    O["original_prefix_certificate"](g, source, path)
    # State/pair caps govern the entry search, which a central source skips.
    # Exercise them on a strict noncentral source with a verified hit.
    search_source = (0, 0, -1, -5, 6)
    assert g.interior(search_source) and not O["central"](g, search_source)
    search_path = O["entry_escape"](g, search_source)
    assert search_path
    O["original_prefix_certificate"](g, search_source, search_path)
    for limits in (dict(state_cap=1), dict(pair_cap=1), dict(step_cap=0)):
        with pytest.raises(ValueError, match="cap"):
            O["entry_escape"](g, search_source, **limits)
    noncentral = (2, 2, 0, 15, -15)
    assert g.interior(noncentral) and not O["central"](g, noncentral)
    with pytest.raises(ValueError, match="domain"):
        O["central_escape"](g, noncentral)
    short = O["Geometry"](-1, 0, 0)
    with pytest.raises(ValueError, match="domain"):
        O["entry_escape"](short, (2, 2, 0, 0, 0))


def test_failed_rank_shortcuts_are_preserved():
    g = O["Geometry"](-1, 0, 0)

    def rank(w):
        a, b, p, q, r = w
        delta = int(a != 1)-int(b != 1)
        return abs(p-delta)+abs(p+q+r)

    cyclic = (2, 1, 1, 3, -5)
    seed = (0, 0, 0, -1, 0)
    source_path = O["replay"](g, seed, [(0, 6), (8, 3), (0, 3), (4, 3)], require_zero=False)
    assert source_path[-1][2] == cyclic
    loop = O["replay"](g, cyclic, [(3, 0), (2, 0), (0, 2), (4, 3)], require_zero=False)
    assert loop[-1][2] == cyclic
    assert rank(cyclic) == 1
    level = {cyclic}
    for _ in range(2):
        level = {child for w in level for _, _, child in g.edges(w)}
        assert min(map(rank, level)) > 0
    productive = O["replay"](g, cyclic, [(3, 0), (4, 3), (6, 1)], require_zero=False)
    assert [rank(e[2]) for e in productive] == [3, 2, 0]

    formal = (0, 0, -1, -5, 6)
    assert g.interior(formal) and rank(formal) == 1
    level = {formal}
    for count, minimum in [(1, 2), (3, 2), (10, 1)]:
        level = {child for w in level for _, _, child in g.edges(w)}
        assert len(level) == count and min(map(rank, level)) == minimum
    path = O["replay"](g, formal, [(0, 9), (0, 9), (0, 0), (9, 0), (1, 2)])
    O["original_prefix_certificate"](g, formal, path)


def test_emitted_source_domain_is_exact():
    geometries = {(k, t): O["Geometry"](-1, k, t) for k, t in O["MEMBERS"]}
    keys = O["expected_native_keys"](geometries)
    assert len(keys) == 665
    assert sum(k[0] == "CENTRAL_PATH" for k in keys) == 315
    assert sum(k[0] == "CYCLE_PATH" for k in keys) == 124
    assert sum(k[0] == "ENTRY_PATH" for k in keys) == 172
    assert sum(k[0] == "TYPED_ENTRY_PATH" for k in keys) == 54


def test_truncated_receipts_refuse(tmp_path):
    path = tmp_path / "truncated.log"
    path.write_text("CLASS_A_SIX_SMALL_ENTRY_PASS 4470 35688 351816\n")
    with pytest.raises(ValueError, match="incomplete"):
        O["check_small_native_log"](path)
    path.write_text("CENTRAL_PATH 0 3 2 2 0 0 0 0\n")
    with pytest.raises(ValueError, match="incomplete"):
        O["check_native_log"](path)
    path.write_text("CENTRAL_PATH 0 3 2 2 0 0 0 0\n" * 2)
    with pytest.raises(ValueError, match="duplicate"):
        O["check_native_log"](path)
    path.write_text("contract-receipt: exact nearest RUN occurrence selection FAILED\n")
    with pytest.raises(ValueError, match="unexpected"):
        O["check_native_log"](path)
    path.write_text("CLASS_A_CENTRAL_ENTRY_PASS members=9 members=9\n")
    with pytest.raises(ValueError, match="duplicate native completion field"):
        O["check_native_log"](path)
    path.write_text("CLASS_A_CENTRAL_ENTRY_PASS members=9 FAILED\n")
    with pytest.raises(ValueError, match="malformed native completion fields"):
        O["check_native_log"](path)
