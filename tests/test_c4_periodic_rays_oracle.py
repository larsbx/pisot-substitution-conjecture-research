"""Exact independent ray overlap replay and full word-prefix witness checks."""

from pathlib import Path
import os
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "reference"))
from psc_research.overlap_graph import OverlapGraph, first_depths
from psc_research.pip_screen import charpoly, irreducible, mat, pisot, primitive


FIXTURES = {
    "left-proper-power": ("01", "02", "0"),
    "phase-zero": ("01", "12", "021"),
    "nonunit-period-two": ("1", "021", "001"),
    "three-cyclic-letters": ("1", "201", "001"),
    "parameter-three": ("1", "01112", "001"),
}


class AlignedGraph(OverlapGraph):
    def __init__(self, sigma, pair, cap=20_000):
        self.pair = pair
        super().__init__(sigma, cap)

    def seeds(self):
        return [(*self.pair, self.F.zero)]

    def endpoint(self, state):
        top, bottom, shift = state
        return shift == self.F.zero or shift == self.F.sub(self.l[top - 1], self.l[bottom - 1])


def rows(images, cap=20_000):
    sigma = {a: tuple(int(c) + 1 for c in image) for a, image in enumerate(images, 1)}
    matrix = mat(sigma)
    coefficients = charpoly(matrix)
    if not (primitive(matrix) and irreducible(*coefficients) and pisot(*coefficients)):
        raise ValueError("source is outside primitive irreducible Pisot hypotheses")
    # Select the cyclic alphabet by taking the stable image of the first map.
    cyclic = set(sigma)
    for _ in sigma:
        cyclic = {sigma[a][0] for a in cyclic}
    for top in sorted(cyclic):
        for bottom in sorted(cyclic):
            if top >= bottom:
                continue
            graph = AlignedGraph(sigma, (top, bottom), cap)
            diagonal = first_depths(graph, graph.is_coincidence)
            boundary = first_depths(graph, graph.endpoint) if diagonal[0] == -1 else [-1]
            top_digits, bottom_digits = [], []
            if diagonal[0] >= 0:
                vertex = 0
                while diagonal[vertex] > 0:
                    upper, lower, offset = graph.states[vertex]
                    scaled = graph.F.mul(graph.F.beta, offset)
                    for i, j in ((i, j) for i in range(len(sigma[upper])) for j in range(len(sigma[lower]))):
                        shift = graph.F.sub(graph.F.add(scaled, graph.prefix[lower, j]), graph.prefix[upper, i])
                        child = sigma[upper][i], sigma[lower][j], shift
                        if graph.overlaps(child) and diagonal[graph.index[child]] == diagonal[vertex] - 1:
                            top_digits.append(i)
                            bottom_digits.append(j)
                            vertex = graph.index[child]
                            break
                    else:
                        raise ValueError("distance lacks a decreasing occurrence")
                assert graph.is_coincidence(graph.states[vertex])
            yield (top - 1, bottom - 1, len(graph.states), sum(map(len, graph.adj)),
                   diagonal[0], -1 if -1 in boundary else max(boundary),
                   tuple(top_digits), tuple(bottom_digits))


def literal_address(images, source, digits):
    marked = [(source, ())]
    for _ in digits:
        marked = [(int(c), address + (i,)) for a, address in marked for i, c in enumerate(images[a])]
    index = next(i for i, (_, address) in enumerate(marked) if address == digits)
    word = tuple(a for a, _ in marked)
    return tuple(word[:index].count(c) for c in range(3)), word[index]


@pytest.mark.parametrize("name", FIXTURES)
def test_complete_exact_graphs_and_literal_witnesses(name):
    images = FIXTURES[name]
    result = list(rows(images))
    assert [(r[0], r[1], r[4], r[5]) for r in result] == EXPECTED[name]
    for top, bottom, states, edges, depth, boundary, top_digits, bottom_digits in result:
        assert states > 1 and edges > 0
        assert len(top_digits) == len(bottom_digits) == depth
        assert literal_address(images, top, top_digits) == literal_address(images, bottom, bottom_digits)


def test_refuses_cap_and_strict_reducible_control():
    with pytest.raises(RuntimeError, match="capped"):
        list(rows(FIXTURES["phase-zero"], cap=1))
    with pytest.raises(ValueError, match="outside"):
        list(rows(("10", "102", "211")))


def test_right_common_endpoint_is_a_closed_overlap_vertex():
    sigma = {1: (2,), 2: (1, 3, 2), 3: (1, 1, 2)}
    graph = AlignedGraph(sigma, (1, 2))
    right_offset = graph.F.sub(graph.l[0], graph.l[1])
    right_only = (1, 2, right_offset)
    assert right_offset != graph.F.zero and graph.overlaps(right_only)
    assert graph.endpoint(right_only)
    assert not graph.overlaps((1, 2, graph.l[0]))  # Bare contact is no graph edge.


def test_native_packet_matches_every_oracle_row():
    native_path = os.environ.get("PSC_PERIODIC_RAY_NATIVE")
    if native_path is None:
        pytest.skip("set PSC_PERIODIC_RAY_NATIVE to compare the native receipt")
    observed = [line for line in Path(native_path).read_text().splitlines() if line.startswith("RAY ")]
    expected = []
    for name, images in FIXTURES.items():
        for row in rows(images):
            fields = " ".join(map(str, row[:6]))
            digits = ["".join(f",{digit}" for digit in side) or "-" for side in row[6:]]
            expected.append(" ".join(("RAY", name, fields, *digits)))
    assert observed == expected


EXPECTED = {
    "left-proper-power": [],
    "phase-zero": [(0, 1, 4, -1)],
    "nonunit-period-two": [(0, 1, 5, -1)],
    "three-cyclic-letters": [(0, 1, 5, -1), (0, 2, 6, -1), (1, 2, 4, -1)],
    "parameter-three": [(0, 1, 2, -1)],
}
