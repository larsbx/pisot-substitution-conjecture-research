"""Independent integer oracle for the canonical minus-boundary template.

Canonical implementation: kernel/psc/class_d_boundary_template.mojo.
This specializes the symbolic graph method using the exact length formulas
in the family note, section 4i. A successful Python replay does not provide
a Mojo execution receipt. Run from the repository root without arguments.
"""
from collections import deque
from pathlib import Path
import json
import sys

FIRST = (0, 1, 1)
LAST = (1, 0, 1)
RUN = ((3, 5), (3, 6), (2, 4))  # slope, intercept
UNIT = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


class Undecided(ValueError):
    """The proposed threshold does not certify a uniform decision."""


def add(u, v):
    return tuple(x + y for x, y in zip(u, v))


def neg(u):
    return tuple(-x for x in u)


def sign(w, floor):
    """Sign certified by coefficients after beta=2*floor+6+z, z>0."""
    c0 = -4*w[0] - 2*w[1]
    c1 = -2*w[0] + 2*w[2]
    c2 = 3*w[0] + 3*w[1] + 2*w[2]
    t = 2*floor + 6
    shifted = (c0 + c1*t + c2*t*t, c1 + 2*c2*t, c2)
    if all(x == 0 for x in shifted):
        return 0
    if all(x >= 0 for x in shifted):
        return 1
    if all(x <= 0 for x in shifted):
        return -1
    raise Undecided(("geometry", w, shifted))


def real(vertex, floor):
    top, bottom, *w = vertex
    return (sign(add(w, UNIT[bottom]), floor) > 0
            and sign(add(UNIT[top], neg(w)), floor) > 0)


def geq(affine, floor):
    """Decide slope*a+base >= 0 for every a>=floor, or refuse."""
    slope, base = affine
    value = slope*floor + base
    if slope >= 0 and value >= 0:
        return True
    if slope <= 0 and value < 0:
        return False
    raise Undecided(("range", affine, floor))


def seeds(floor):
    out = set()
    for a in range(3):
        for b in range(a+1, 3):
            for top, top_start in ((a, (0, 0, 0)), (b, UNIT[a])):
                for bottom, bottom_start in ((b, (0, 0, 0)), (a, UNIT[b])):
                    vertex = (top, bottom, *add(bottom_start, neg(top_start)))
                    if real(vertex, floor):
                        out.add(vertex)
    return sorted(out)


def segment(letter, part):
    """Child letter, constant prefix vector, affine y-prefix contribution."""
    child = (FIRST[letter], 2, LAST[letter])[part]
    prefix = UNIT[FIRST[letter]] if part else (0, 0, 0)
    return child, prefix, RUN[letter] if part == 2 else (0, 0)


def children(vertex, floor):
    top, bottom, x, y, z = vertex
    if top == bottom and (x, y, z) == (0, 0, 0):
        return set()  # coincident overlaps are terminal in this graph
    out = set()
    base_xy = (x+y, x+y+2*z)
    base_z = (3*x+3*y+2*z, 5*x+6*y+4*z)
    for top_part in range(3):
        top_child, top_prefix, top_affine = segment(top, top_part)
        for bottom_part in range(3):
            bottom_child, bottom_prefix, bottom_affine = segment(bottom, bottom_part)
            u = base_xy[0] + bottom_prefix[0] - top_prefix[0]
            v = base_xy[1] + bottom_prefix[1] - top_prefix[1]
            slope = base_z[0] + bottom_affine[0] - top_affine[0]
            base = base_z[1] + bottom_affine[1] - top_affine[1]
            lower = (-RUN[top][0], 1-RUN[top][1]) if top_part == 1 else (0, 0)
            upper = (RUN[bottom][0], RUN[bottom][1]-1) if bottom_part == 1 else (0, 0)
            bound = 2 + 2*(abs(u)+abs(v))
            if bound > 100:
                raise RuntimeError("COORDINATE_BUDGET_EXHAUSTED")
            for c in range(-bound, bound+1):
                child = (top_child, bottom_child, u, v, c)
                if not real(child, floor):
                    continue
                # m=c-(slope*a+base). Every integer in [lower,upper]
                # is realized by differences of actual segment positions.
                if (geq((-slope-lower[0], c-base-lower[1]), floor)
                        and geq((upper[0]+slope, upper[1]-c+base), floor)):
                    out.add(child)
    return out


def build(floor=4, cap=20000):
    if not 0 <= floor <= 64 or not 1 <= cap <= 20000:
        raise ValueError("outside declared threshold/state budget")
    roots = seeds(floor)
    queue = deque(roots)
    seen = set(roots)
    graph = {}
    while queue:
        if len(seen) > cap:
            raise RuntimeError("STATE_BUDGET_EXHAUSTED")
        vertex = queue.popleft()
        graph[vertex] = children(vertex, floor)
        for child in sorted(graph[vertex]):
            if child not in seen:
                seen.add(child)
                queue.append(child)
    return graph


def depths(graph):
    reverse = {v: set() for v in graph}
    depth = {v: 0 for v in graph if v[2:] == (0, 0, 0)}
    for vertex, successors in graph.items():
        for child in successors:
            reverse[child].add(vertex)
    queue = deque(depth)
    while queue:
        vertex = queue.popleft()
        for parent in reverse[vertex]:
            if parent not in depth:
                depth[parent] = depth[vertex] + 1
                queue.append(parent)
    return depth


def check_exact_support(graph, a):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from class_d_boundary_probe import labelled_support
    if graph != labelled_support(a):
        raise ValueError("labelled directed support differs")


def report():
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from class_d_boundary_probe import probe
    floor = 4
    graph = build(floor)
    depth = depths(graph)
    if set(depth) != set(graph):
        raise ValueError("symbolic target-free vertex")
    finite_prefix = [probe(-1, a) for a in range(floor)]
    if any(row["missing"] for row in finite_prefix):
        raise ValueError("finite-prefix target-free vertex")
    for a in (4, 8):
        check_exact_support(graph, a)
    vertices = sorted(graph)
    index = {v: i for i, v in enumerate(vertices)}
    return {
        "status": "INDEPENDENT_SYMBOLIC_REPLAY_COMPLETE",
        "authority": "independent-exact-integer-python-oracle",
        "canonical_execution": "NOT_RUN_LOCALLY",
        "canonical_replay": "kernel/class_d_boundary_certificate.mojo",
        "scope": "s=-1, b=0, all integer a>=0; closure candidate pending canonical receipt",
        "symbolic_floor": floor,
        "symbolic_vertices": len(vertices),
        "symbolic_directed_edges": sum(map(len, graph.values())),
        "max_half_depth": max(depth.values()),
        "full_support_crosschecks": [4, 8],
        "finite_prefix": finite_prefix,
        "vertex_cap": 20000,
        "coordinate_candidate_cap": 100,
        "rng": "NONE",
        "vertices": vertices,
        "seeds": [index[v] for v in seeds(floor)],
        "adjacency": [sorted(index[w] for w in graph[v]) for v in vertices],
        "depths": [depth[v] for v in vertices],
    }


if __name__ == "__main__":
    if sys.argv[1:]:
        raise ValueError("usage: class_d_boundary_template.py")
    print(json.dumps(report(), indent=2))
