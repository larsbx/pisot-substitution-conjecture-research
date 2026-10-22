"""Structural independent audit of the candidate; finite fixtures are not a theorem."""
from collections import defaultdict
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "kernel/psc/class_a_typed_carrier.mojo"
FIXTURES = ROOT / "evidence/class-a-run-index-2026-10-21"


def rows():
    source = SOURCE.read_text()
    matches = re.findall(
        r"^\s+List\[Int\]\(\[(-?\d+(?:,-?\d+){7})\]\),$",
        source, re.MULTILINE,
    )
    result = [tuple(map(int, match.split(","))) for match in matches]
    if len(result) != 89:
        raise ValueError("missing or extra typed intervals")
    return result


def covered(n, template):
    if n < 4:
        raise ValueError("n>=4 required")
    states = set()
    for top, bottom, s, y, al, bl, au, bu in template:
        lo, hi = al*n+bl, au*n+bu
        if lo > hi:
            raise ValueError("empty interval")
        for k in range(lo, hi+1):
            label = (top, bottom, k, s-k-y, y)
            if label in states:
                raise ValueError("overlapping typed intervals")
            states.add(label)
    return states


def fixture(n):
    lines = (FIXTURES / f"graph-n{n}.log").read_text().splitlines()
    vertices, edges, seeds, summaries = {}, [], [], []
    for line in lines:
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "V":
            data = list(map(int, parts[1:]))
            if len(data) != 8 or data[0] != n or data[1] in vertices:
                raise ValueError("malformed/duplicate exact vertex")
            _, i, top, bottom, k, c, y, depth = data
            if depth < 0:
                raise ValueError("finite non-hitting vertex")
            vertices[i] = (top, bottom, k, c, y)
        elif parts[0] == "E":
            data = list(map(int, parts[1:]))
            if len(data) != 5 or data[0] != n:
                raise ValueError("malformed occurrence")
            edges.append(data[1:])
        elif parts[0] == "SEED":
            data = list(map(int, parts[1:]))
            if len(data) != 2 or data[0] != n:
                raise ValueError("malformed seed")
            seeds.append(data[1])
        elif parts[0] == "SUMMARY":
            data = list(map(int, parts[1:]))
            if len(data) != 6 or data[0] != n:
                raise ValueError("malformed summary")
            summaries.append(data)
    if len(summaries) != 1 or set(vertices) != set(range(len(vertices))):
        raise ValueError("incomplete exact graph export")
    if summaries[0][1] != len(vertices):
        raise ValueError("summary size mismatch")
    if len(set(vertices.values())) != len(vertices):
        raise ValueError("duplicate exact label")
    if any(a not in vertices or b not in vertices or i < 0 or j < 0 for a,b,i,j in edges):
        raise ValueError("invalid ordered occurrence")
    if any(seed not in vertices for seed in seeds):
        raise ValueError("missing seed")
    return set(vertices.values()), summaries[0], len(edges)


def test_uniform_cardinality_of_formal_candidate():
    template = rows()
    groups = defaultdict(list)
    for top, bottom, s, y, al, bl, au, bu in template:
        assert 0 <= top <= 2 and 0 <= bottom <= 2
        assert au-al >= 0 and (au-al)*4+bu-bl >= 0
        groups[top,bottom,s,y].append((al,bl,au,bu))
    assert len(groups) == 75
    # Each pair of affine intervals stays ordered and disjoint for every n>=4.
    for intervals in groups.values():
        intervals.sort(key=lambda a: (a[0]*4+a[1], a[2]*4+a[3]))
        for (_,_,au,bu), (al,bl,_,_) in zip(intervals, intervals[1:]):
            assert al-au >= 0 and (al-au)*4+bl-bu >= 1
    slope = sum(au-al for _,_,_,_,al,bl,au,bu in template)
    constant = sum(bu-bl+1 for _,_,_,_,al,bl,au,bu in template)
    assert (slope, constant) == (40,115)


def test_exact_archived_complete_graphs():
    for n, size, max_depth, edge_count in [(4,275,5,1778), (18,835,15,17178)]:
        expected, summary, n_edges = fixture(n)
        assert n_edges == edge_count
        assert (summary[1], summary[2]) == (size,max_depth)
        assert covered(n,rows()) == expected


def test_negative_controls():
    candidate = rows()
    assert (0,1,-5,8,-2) not in covered(4,candidate)
    assert (0,2,-4,7,-1) not in covered(4,candidate)
    assert (1,2,4,-4,0) in covered(4,candidate)
    import pytest
    assert covered(4,candidate[:-1]) != fixture(4)[0]
    with pytest.raises(ValueError):
        covered(4,candidate+[candidate[0]])
    with pytest.raises(ValueError):
        covered(3,candidate)
