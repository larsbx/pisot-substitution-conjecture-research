"""Independent 117-member replay of the four literal U-hit occurrences.

Use the unchanged shared rational Geometry. These specimens are a
regression for the separately quantified symbolic certificate, not a
proof by exhaustive sampling of an unbounded chamber.
"""
import runpy
from pathlib import Path

root = Path(__file__).resolve().parents[1]
oracle = runpy.run_path(str(root / "oracles/python/class_a_boundary_U_hit.py"))
Geometry = oracle["Geometry"]
witness = oracle["witness"]


def reverse(w):
    return (w[1], w[0], *(-x for x in w[2:]))


def test_all_four_actual_occurrences_and_reversals_on_117_members():
    total = 0
    for k in range(13):
        for t in range(9):
            record = witness(k, t)
            g = Geometry(-1, k, t)
            parent = (0, 1, 0, 0, 0)
            expected = [(1, 2), (0, t + 1), (g.d + 3, 0), (1, 2)]
            assert [(s["i"], s["j"]) for s in record["steps"]] == expected
            for step in record["steps"]:
                i, j, target = step["i"], step["j"], step["target"]
                assert step["parent"] == parent
                assert g.child(parent, i, j) == target
                assert g.interior(parent) and g.interior(target)
                assert g.child(reverse(parent), j, i) == reverse(target)
                assert g.interior(reverse(parent)) and g.interior(reverse(target))
                parent = target
                total += 1
            assert parent == (2, 2, 0, 0, 0)
            assert g.child((2, 0, 0, -1, 1), 1, 1) != parent
    assert total == 117 * 4
