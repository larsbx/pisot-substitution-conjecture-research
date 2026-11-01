"""Scope-limited canonical frontier audit for the two recovered class-A images.

All geometry/witness checks use the existing independent Fraction oracles.
This is *not* a graph closure test, a seed reachability theorem, or PSC.
"""
from functools import lru_cache
import json
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[2]
ORACLES = ROOT / "oracles" / "python"
C = (2, 2, 0, 0, 0)
CY = (1, 2, 0, -2, 2)
CC = (1, 1, 0, -2, 3)


def reverse(w):
    return (w[1], w[0], *(-v for v in w[2:]))


@lru_cache(None)
def source_module(name):
    return runpy.run_path(str(ORACLES / ("class_a_boundary_" + name + ".py")))


def both_orientations(labels):
    raw = {tuple(w) for w in labels}
    return raw | {reverse(w) for w in raw}


def registered_source_families():
    """Explicit source registry: only complete-star families named below.

    This list is not a claim to enumerate *all* complete-star sources
    anywhere in main or in the unmerged downstream research stacks.
    """
    specs = (("p3_children", 6), ("tx_children", 6), ("p_children", 10),
             ("e_children", 6), ("e2_children", 4),
             ("h3_children", 8), ("h5_children", 2),
             ("f_children", 8))
    rows = {name: both_orientations(
        source_module(name)["source"](i) for i in range(count))
        for name, count in specs}
    rows["w_children"] = both_orientations(source_module("w_children")["SOURCES"])
    rows["u_children"] = both_orientations([source_module("u_children")["U"]])
    rows["h4_children"] = both_orientations([(0, 2, 0, -2, 4)])
    rows["tm_children"] = both_orientations([(2, 2, -1, 1, 1),
                                               (2, 2, -1, 1, 2)])
    return rows


def snapshot():
    p3 = {tuple(x) for x in source_module("p3_children")["envelope"]()}
    tx = {tuple(x) for x in source_module("tx_children")["envelope"]()}
    catalog = registered_source_families()
    registered = set().union(*catalog.values())
    union = p3 | tx
    known = union & registered
    terminal = union & {C}
    review = union - known - terminal
    return {
        "scope": "two chamber-wide outgoing images, not forward closure or all seed-reachable states",
        "p3_image": len(p3), "tx_image": len(tx),
        "intersection": len(p3 & tx), "tx_only": len(tx - p3),
        "union": len(union), "registered_sources": len(known),
        "typed_terminal": len(terminal), "unclassified_in_this_registry": len(review),
        "registered_source_labels": [list(x) for x in sorted(known)],
        "frontier_review_labels": [list(x) for x in sorted(review)],
        "source_family_intersections": {name: len(union & rows)
                                        for name, rows in sorted(catalog.items())},
        "review_includes_cy": CY in review,
        "review_includes_cc": CC in review,
        "finite_witnesses_not_universal_proof": True,
        "forward_closed": False,
        "universal_BH": False,
    }


def replay_archived_first_witnesses():
    """Replay one occurrence for each envelope label from each original packet.

    These are the *recorded first witnesses* from 117-cell source searches.
    Do not mistake their successful replay for complete all-parameter stars.
    """
    witness_count = 0
    for name, folder in (("p3_children", "class-a-boundary-p3-2026-10-28"),
                         ("tx_children", "class-a-boundary-tx-2026-10-28")):
        module = source_module(name)
        receipt = json.loads((ROOT / "evidence" / folder / "probe.json").read_text())
        expected = {tuple(w) for w in module["envelope"]()}
        got = set()
        for row in receipt["witnesses"]:
            target = tuple(row["target"])
            k, t, kind, i, j = (row[field] for field in ("k", "t", "kind", "i", "j"))
            g = source_module("children")["Geometry"](-1, k, t)
            source = tuple(module["source"](kind))
            assert module["predicted"](kind, g, i, j)
            assert g.interior(source) and g.interior(target)
            assert g.child(source, i, j) == target
            assert g.child(reverse(source), j, i) == reverse(target)
            assert g.interior(reverse(target))
            assert target not in got, ("duplicate receipt witness", name, target)
            got.add(target)
            witness_count += 1
        assert got == expected, (name, len(got), len(expected))
    return witness_count


def replay_interface_grid():
    """Selected exact real-word interfaces; never extrapolate the grid."""
    p3 = (0, 2, 1, 3, -4)
    q3 = (0, 2, 1, -1, 1)
    x = (0, 0, 1, 0, -1)
    y0 = (2, 2, 1, -1, -1)
    Geometry = source_module("children")["Geometry"]
    tx = source_module("tx_children")
    for k, t in ((0, 0), (0, 1), (1, 0), (2, 2), (4, 3)):
        g = Geometry(-1, k, t)
        A = g.n + g.d
        assert g.child(p3, A + 1, g.n - 2) == q3
        assert g.child(q3, A + 1, 0) == x
        assert g.child(x, A + 1, g.n + 1) == q3
        assert g.child(x, g.d + 3, 1) == y0
        assert g.child(y0, g.n, k + 2) == CY and g.interior(CY)
        assert g.interior(g.child(y0, g.n, g.n)) == (t == 0)
        if t == 0:
            assert g.child(y0, g.n, g.n) == CC
        for kind, length in ((0, 3), (2, 2), (4, 3)):
            path = tx["path"](kind, g)
            assert len(path) == length
            tx["verify_packet"](kind, g, path)


def probe():
    summary = snapshot()
    assert (summary["p3_image"], summary["tx_image"], summary["intersection"],
            summary["tx_only"], summary["union"]) == (37, 42, 20, 22, 59)
    assert (summary["registered_sources"], summary["typed_terminal"],
            summary["unclassified_in_this_registry"]) == (24, 1, 34)
    assert summary["review_includes_cy"] and summary["review_includes_cc"]
    assert replay_archived_first_witnesses() == 79
    replay_interface_grid()
    return summary


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2, sort_keys=True))
