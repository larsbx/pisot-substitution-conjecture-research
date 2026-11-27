"""Independent, literal replays of the determinant-three BPA certificate."""

import os
from pathlib import Path

import pytest

from test_c4_strict_period_oracle import cuts, row


SEED = ("01", "10")
SOURCE = (Path(__file__).resolve().parents[1] / "kernel" / "tests" /
          "test_c4_determinant_three_carrier.mojo")


def substitution(k):
    return "1", "0" + "1" * k + "2", "0001"


def literal_graph(k):
    sigma = substitution(k)
    vertices = [SEED]
    seen = {SEED}
    edges = {}
    for parent in vertices:
        assert len(vertices) <= 1200
        assert sum(len(sigma[int(a)]) for a in parent[0]) <= 100000
        children = [child for _, _, child in row(sigma, parent)]
        edges[parent] = children
        for child in children:
            if child not in seen:
                vertices.append(child)
                seen.add(child)
    return edges


@pytest.mark.parametrize(("k", "states", "edges", "longest", "max_depth"), [
    (3, 587, 66538, 9531, 2),
    (4, 243, 10983, 264, 1),
    (5, 65, 1636, 44, 1),
    (6, 57, 2171, 49, 1),
    (7, 57, 3136, 54, 1),
    (8, 57, 4293, 59, 1),
    (9, 57, 5642, 64, 1),
    (16, 57, 20461, 99, 1),
])
def test_exact_ordered_boundary_closure(k, states, edges, longest, max_depth):
    graph = literal_graph(k)
    assert (len(graph), sum(map(len, graph.values()))) == (states, edges)
    assert max(len(top) for top, _ in graph) == longest
    assert {a for a, b in graph if a == b} == {"0", "1", "2"}

    productive = {p for p in graph if p[0] == p[1]}
    for _ in range(max_depth):
        assert len(productive) < len(graph)
        productive |= {p for p, children in graph.items()
                       if any(child in productive for child in children)}
    assert productive == graph.keys()

    if native := os.environ.get("PSC_DET3_NATIVE"):
        expected = f"det3 {k} {states} {edges} {longest} {max_depth}"
        assert expected in Path(native).read_text().splitlines()


def expanded_table(k):
    table = SOURCE.read_text().split('comptime TABLE = """', 1)[1].split('"""', 1)[0]
    rows = [line.split(" | ") for line in table.strip().splitlines()]
    states = [tuple(word.replace("I", "1" * k).replace("H", "1" * (k - 3))
                    for word in parent.split()) for parent, _ in rows]

    def affine(token):
        return k + int(token[1:] or "0") if token.startswith("k") else int(token)

    for pair, (_, children) in zip(states, rows, strict=True):
        expected = []
        for token in children.split():
            if token == "-":
                continue
            diagonal, colon, child = token.partition(":")
            if not colon:
                diagonal, child = "0", diagonal
            target, _, count = child.partition("*")
            representative = states[int(target.rstrip("'"))]
            oriented = representative[::-1] if target.endswith("'") else representative
            expected += ([("1", "1")] * affine(diagonal) + [oriented]) * affine(count or "1")
        yield pair, expected


@pytest.mark.parametrize("k", [8, 9, 10, 16, 31])
def test_symbolic_row_instantiations_agree_occurrence_for_occurrence(k):
    sigma = substitution(k)
    for pair, expected in expanded_table(k):
        assert list(cuts(*pair)) == [0, len(pair[0])]
        if pair[0] == pair[1]:
            assert not expected
            continue
        assert [child for _, _, child in row(sigma, pair)] == expected
