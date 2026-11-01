"""Unit descent and guards, independently of the generic polynomial fit."""
import json
from pathlib import Path
import runpy
import pytest

ROOT = Path(__file__).resolve().parents[1]
M = runpy.run_path(str(ROOT / "oracles/python/class_a_x_transfer_plane.py"))
S = runpy.run_path(str(ROOT / "oracles/python/class_a_x_transfer_plane_symbolic.py"))
PACKET = ROOT / "evidence/class-a-x-transfer-plane-2026-10-31"


def test_all_local_paths_and_finite_profile_replay():
    actual = dict(paths=M["replay"](), finite_profile=M["profile"](),
                  plane_counterexample=M["plane_counterexample"]())
    recorded = json.loads((PACKET / "probe.json").read_text())
    assert json.loads(json.dumps(actual)) == recorded
    assert actual["paths"]["specimens"] == 120
    assert actual["paths"]["oriented_paths"] == 1090
    assert actual["paths"]["selected_edges"] == 17536
    assert actual["paths"]["exceptional_base_oriented_paths"] == 240
    assert actual["paths"]["exceptional_base_selected_edges"] == 480
    assert len(actual["finite_profile"]["members"]) == 22
    row = next(r for r in actual["finite_profile"]["members"] if (r["k"], r["t"]) == (0, 8))
    assert row["p_indices_in_x_closure"] == list(range(11))
    assert row["reached_labels_outside_previous_ladder_carrier"] == 40
    assert row["parameter_uniform_reachable_interval_proved"] is False


def test_unbounded_symbolic_identities_and_guard_mutations():
    result = S["certify"]()
    assert result["unbounded_integer_guard_chambers"] == 4
    assert result["generic_guard_free_productivity"] is False
    with pytest.raises(ValueError):
        S["zero"](S["p"]*(S["p"]-1))
    with pytest.raises(ValueError):
        S["nonnegative"](1-S["p"], (S["p"],))


def test_the_origin_last_and_adjacent_run_endpoint():
    path = M["unit_path"](0, 0, 1)
    assert path[1][2:] == (9, M["E"])
    g = M["Geometry"](-1, 0, 0)
    assert g.child(path[1][0], 0, 9) == M["E"]
    with pytest.raises(ValueError):
        M["verify_edges"](g, M["generic_packet"](0, 0, 1, 0, 1))
    nxt = M["unit_path"](0, 1, 1)
    assert nxt[1][2] == 11  # A: still the final RUN y, not LAST x.
    assert nxt[1][3] == M["source"](1, 0, 0)
    assert M["unit_path"](0, 0, 6)[0][1] == 1
    assert M["source"](1, 0, 0) != M["E"]


def test_plane_membership_does_not_waive_occurrence_bounds():
    c = M["plane_counterexample"]()
    assert c["source"] == (0, 2, 1, 6, -9)
    assert len(c["x_to_source_path"]) == 9
    assert c["all_three_formal_labels_strict"] is True
    g = M["Geometry"](-1, 0, 0)
    packet = M["generic_packet"](0, 0, 1, 1, 1)
    M["verify_edges"](g, packet[:1])
    assert packet[1][2] == len(g.words[0])+1
    with pytest.raises(ValueError):
        M["verify_edges"](g, packet)


def test_domain_type_offset_and_true_reversal_controls():
    for k, t, p in [(-1, 0, 0), (0, -1, 0), (0, 0, -1), (0, 0, 7)]:
        with pytest.raises(ValueError):
            M["unit_path"](k, t, p)
    g = M["Geometry"](-1, 0, 0)
    path = M["unit_path"](0, 0, 1)
    bad = list(path)
    a, i, j, b = bad[1]
    bad[1] = (a, i, j, (0, 2, 0, 1, 0))
    with pytest.raises(ValueError):
        M["BASE"]["verify_path"](g, bad)
    bad = [(M["reverse"](a), i, j, M["reverse"](b)) for a, i, j, b in path]
    with pytest.raises(ValueError):
        M["BASE"]["verify_path"](g, bad)
    bad = list(path)
    a, i, j, b = bad[0]
    bad[0] = (a, i, j, (*b[:4], b[4]+1))
    with pytest.raises(ValueError):
        M["BASE"]["verify_path"](g, bad)


def test_previous_two_step_ladder_is_a_specialization():
    for k, t in ((0, 2), (1, 0), (3, 0), (0, 20)):
        g = M["Geometry"](-1, k, t)
        for m in range(2, (k+t+6)//(k+1)+1):
            got = M["generic_packet"](k, t, 2, 0, 2*m)
            old = M["BASE"]["ladder_path"](k, t, m)[:2]
            assert got == old
            M["verify_edges"](g, got)
