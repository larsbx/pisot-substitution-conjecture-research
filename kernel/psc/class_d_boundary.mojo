"""Bounded replay of the two residual class-D b=0 families; no universal verdict."""
from psc.overlap_seed_patch import build_seed_overlap_graph, first_left_aligned_depths


def boundary_member(s: Int, a: Int) raises -> List[List[Int]]:
    # The explicit parameter limit is a resource guard, not a PIP condition.
    if (s != 1 and s != -1) or a < 0 or a > 8:
        raise Error("boundary probe requires s=+/-1 and 0<=a<=8")
    var p = 4 + 3*a - s
    var q = 4 + 3*a - 2*s
    var r = 2 + 2*a - 2*s
    var x: List[Int] = [0]
    var c: List[Int] = [1]
    var y: List[Int] = [1]
    for _ in range(p):
        x.append(2)
    for _ in range(q):
        c.append(2)
    for _ in range(r):
        y.append(2)
    x.append(1)
    c.append(0)
    y.append(1)
    var out = List[List[Int]]()
    out.append(x^)
    out.append(c^)
    out.append(y^)
    return out^


def boundary_probe(s: Int, a: Int, max_states: Int = 20000) raises -> List[Int]:
    if max_states < 1 or max_states > 20000:
        raise Error("boundary probe state cap must be in 1..20000")
    var graph = build_seed_overlap_graph(boundary_member(s, a), max_states)
    if graph.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no boundary-hitting verdict")
    var depths = first_left_aligned_depths(graph)
    var missing = 0
    var deepest = 0
    for i in range(len(depths)):
        if depths[i] < 0:
            missing += 1
        else:
            deepest = max(deepest, depths[i])
    return [4+3*a-s, 4+3*a-2*s, 2+2*a-2*s, graph.size(), deepest, missing]
