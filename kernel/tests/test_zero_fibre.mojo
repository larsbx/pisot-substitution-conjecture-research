"""Replay the zero-fibre comparisons by literal expansion over Z^3.

The three fixed fixtures cover a seam-only catalogue, a unit interior
fixed point, and all eight phases of a nonunit interior cycle.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.h1_census import incidence_rows
from psc.zero_fibre import OriginPatch, compare_zero_fibre


struct Edge(Copyable, Movable, Equatable):
    var label: Int
    var start: List[Int]

    def __init__(out self, label: Int, start: List[Int]):
        self.label = label
        self.start = start.copy()

    def __eq__(self, other: Edge) -> Bool:
        return self.label == other.label and self.start == other.start

    def __ne__(self, other: Edge) -> Bool:
        return not (self == other)


def seed_edges(patch: OriginPatch) -> List[Edge]:
    var edges = List[Edge]()
    if patch.before >= 0:
        var start = List[Int](length=3, fill=0)
        start[patch.before] = -1
        edges.append(Edge(patch.before, start))
    edges.append(Edge(patch.cut.letter, [-patch.cut.v0, -patch.cut.v1, -patch.cut.v2]))
    return edges^


def inflate(sigma: List[List[Int]], m: Mat3, edges: List[Edge]) -> List[Edge]:
    var out = List[Edge]()
    for edge in edges:
        var start = m.apply(edge.start)
        for label in sigma[edge.label]:
            out.append(Edge(label, start))
            start[label] += 1
    return out^


def shares_edge(top: List[Edge], bottom: List[Edge]) -> Bool:
    for edge in top:
        if edge in bottom:
            return True
    return False


def contains_patch(path: List[Edge], patch: List[Edge]) -> Bool:
    for edge in patch:
        if edge not in path:
            return False
    return True


def replay(
    sigma: List[List[Int]],
    determinant: Int,
    seam_count: Int,
    interior_period: Int,
    depths: List[Int],
) raises:
    var result = compare_zero_fibre(sigma)
    var m = Mat3(incidence_rows(sigma))
    assert_equal(m.det(), determinant)
    assert_equal(len(result.patches), len(depths))
    assert_equal(result.depths, depths)
    assert_true(result.all_meet_reference())

    var reference = seed_edges(result.patches[0])
    for i in range(len(result.patches)):
        var patch = result.patches[i]
        assert_equal(patch.before >= 0, i < seam_count)
        if patch.before < 0:
            assert_equal(patch.period, interior_period)
        for j in range(i):
            var prior = result.patches[j]
            assert_false(prior.before == patch.before and prior.cut == patch.cut)

        var seed = seed_edges(patch)
        var path = seed.copy()
        for n in range(1, patch.period + 1):
            path = inflate(sigma, m, path)
            assert_equal(contains_patch(path, seed), n == patch.period)

        var top = reference.copy()
        var bottom = seed.copy()
        for _ in range(depths[i]):
            assert_false(shares_edge(top, bottom))
            top = inflate(sigma, m, top)
            bottom = inflate(sigma, m, bottom)
        assert_true(shares_edge(top, bottom))
    print(sigma, "det", determinant, "seams", seam_count,
          "interior", len(depths) - seam_count, "depths", depths)


def main() raises:
    replay([[0, 1], [0, 2], [0]], 1, 3, 0, [0, 0, 0])
    replay([[0, 1], [1, 2], [0, 2, 1]], 1, 4, 1, [0, 0, 0, 4, 1])
    var nonunit: List[List[Int]] = [[1], [0, 1, 2], [0, 0, 1]]
    replay(nonunit, 2, 4, 8, [0, 0, 0, 3, 5, 6, 6, 8, 5, 6, 6, 4])

    var graph_refused = False
    try:
        _ = compare_zero_fibre(nonunit, max_overlap_states=1)
    except e:
        graph_refused = "capped partial graph" in String(e)
    assert_true(graph_refused)

    var box_refused = False
    try:
        _ = compare_zero_fibre(nonunit, max_prototile_states=1)
    except e:
        box_refused = "state cap reached" in String(e)
    assert_true(box_refused)

    var reducible_refused = False
    try:
        _ = compare_zero_fibre([[1, 0], [1, 0, 2], [2, 1, 1]])
    except e:
        reducible_refused = "primitive irreducible Pisot" in String(e)
    assert_true(reducible_refused)
    require_contract("zero-fibre seam and interior periods and first common descendants at exact integer positions. Inconclusive caps and reducible input refuse")
