"""Evidence and counter-calibrations for the new scoped productivity work."""
import copy
import json
from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
M = runpy.run_path(str(ROOT / "oracles/python/class_a_x_productivity.py"))


def test_complete_orientation_graphs_match_recorded_certificate():
    recorded = json.loads((ROOT / "evidence/class-a-x-productivity-2026-10-31/finite-certificates.json").read_text())
    assert [(r["k"], r["t"]) for r in recorded["members"]] == list(M["MEMBERS"])
    for expected in recorded["members"]:
        actual = M["audit"](expected["k"], expected["t"], certificate=True)
        # JSON normalizes tuple/list representation; compare all witnesses too.
        assert json.loads(json.dumps(actual)) == expected
        assert not actual["unproductive_labels"]
        assert not actual["nonterminal_not_returning_x"]
        assert not actual["nonproductive_sink_sccs"]
        assert actual["no_run_run_unproductive"] == 0
        assert actual["corners_only_unproductive"] > 0
        assert actual["recurrent_sccs"] == 1
        assert actual["sink_sccs"] == 2
        assert actual["exceptions"] in ([], [M["reverse"](M["E"]), M["E"]])
        assert actual["universal_x_productivity"] is False
    row = next(r for r in recorded["members"] if (r["k"], r["t"]) == (3, 0))
    assert (row["x_vertices"], row["nine_vertices"], row["vertices"]) == (350, 351, 352)


def test_cap_and_typed_terminal_refusals():
    with pytest.raises(M["IncompleteGraph"]):
        M["audit"](0, 0, cap=18)
    with pytest.raises(ValueError):
        M["audit"](-1, 0)
    assert not M["coincidence"]((0, 2, 0, 0, 0))
    assert not M["coincidence"]((0, 0, 0, 1, 0))
    g = M["Geometry"](-1, 0, 0)
    assert len(M["swap_sources"](g)[1]) == 18


def test_bad_sink_and_recurrent_good_exit():
    # Abstract controls guard the algorithm, not the actual overlap theorem.
    bad = [[(0, 0, 0)], []]
    assert set(M["backwards"](bad, [1])[0]) == {1}
    good = [[(0, 0, 0), (1, 1, 2)], []]
    assert M["backwards"](good, [1])[0] == {1: 0, 0: 1}
    assert sorted(map(len, M["components"](good))) == [1, 1]


def test_ladder_paths_large_parameters_and_boundary_indices():
    checks = edges = 0
    members = [(k, t) for k in range(13) for t in range(9)] + [(0, 20), (0, 64), (32, 0)]
    for k, t in members:
        if 2*k+t < 2:
            continue
        g = M["Geometry"](-1, k, t)
        for m in range(1, (k+t+6)//(k+1)+1):
            for flip in (False, True):
                path = M["ladder_path"](k, t, m, flip)
                M["verify_path"](g, path)
                assert len(path) == 2*m+4
                checks += 1
                edges += len(path)
        with pytest.raises(ValueError):
            M["ladder_path"](k, t, (k+t+6)//(k+1)+1)
    assert checks > 600 and edges > 10000
    # The sharp transfer lower endpoint i=1 and upper endpoint j=A.
    assert M["ladder_path"](0, 2, 8)[0][1:3] == (1, 0)
    assert M["ladder_path"](0, 2, 2)[1][2] == 14


def test_wrong_endpoint_type_offset_and_reversal_are_rejected():
    for t in (0, 1):
        with pytest.raises(ValueError):
            M["ladder_path"](0, t, 1)
    # At (0,1), the base index is LAST x, not the claimed RUN y.
    g = M["Geometry"](-1, 0, 1)
    actual = g.child(M["ladder_a"](1), g.n+g.d+1, 0)
    assert actual == (0, 0, -1, -4, 6)
    assert actual != (2, 0, -1, -4, 6)
    with pytest.raises(ValueError):
        M["verify_path"](g, [(M["ladder_a"](1), 12, 0, (2, 0, -1, -4, 6))])
    g = M["Geometry"](-1, 0, 2)
    path = M["ladder_path"](0, 2, 2)
    for field in (1, 3):
        bad = copy.deepcopy(path)
        a, i, j, b = bad[0]
        bad[0] = (a, i+1, j, b) if field == 1 else (a, i, j, (*b[:4], b[4]+1))
        with pytest.raises(ValueError):
            M["verify_path"](g, bad)
    bad = [(M["reverse"](a), i, j, M["reverse"](b)) for a, i, j, b in path]
    with pytest.raises((ValueError, AssertionError)):
        M["verify_path"](g, bad)


def test_forest_requires_actual_edges_and_strict_rank_descent():
    g = M["Geometry"](-1, 3, 0)
    _, seeds = M["swap_sources"](g)
    states, ids, adj = M["complete_graph"](g, seeds)
    targets = {v for v, w in enumerate(states) if M["coincidence"](w)}
    d, via = M["backwards"](adj, targets)
    v = next(iter(via))
    bad = dict(d)
    bad[v] += 1
    with pytest.raises(ValueError):
        M["verify_forest"](g, states, adj, bad, via, targets)
    broken = dict(via)
    w, i, j = via[v]
    broken[v] = (w, i+1000, j)
    with pytest.raises(ValueError):
        M["verify_forest"](g, states, adj, d, broken, targets)


def test_symbolic_coefficients_and_mutated_type_rejection():
    symbolic = runpy.run_path(str(ROOT / "oracles/python/class_a_x_ladder_symbolic.py"))
    assert symbolic["certify"]()["symbolic_directed_edges"] == 16
    with pytest.raises(ValueError):
        symbolic["check_edge"]((0, 2, 2, 7, -11), "LAST", symbolic["A"]+1,
                               "FIRST", 0, (2, 0, -1, -4, 6))
    with pytest.raises(ValueError):
        symbolic["zero"](symbolic["m"] * (symbolic["m"]-1))


def test_native_comparison_refuses_incomplete_or_duplicate_emissions(tmp_path):
    p = tmp_path / "bad-native.log"
    p.write_text("X_VERTEX 0 0 0 0 0 0 0 0\n")
    with pytest.raises(ValueError):
        M["compare_native"](p)
    p.write_text("X_VERTEX 0 0 0 0 0 0 0 0\n" * 2)
    with pytest.raises(ValueError):
        M["compare_native"](p)
