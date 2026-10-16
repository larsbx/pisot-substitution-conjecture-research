"""Independent integer oracle for both canonical boundary templates.

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
UNIT = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def run(letter, s):
    return ((3, 4-s), (3, 4-2*s), (2, 2-2*s))[letter]


class Undecided(ValueError):
    """The proposed threshold does not certify a uniform decision."""


def add(u, v):
    return tuple(x + y for x, y in zip(u, v))


def neg(u):
    return tuple(-x for x in u)


def sign(w, floor, s=-1):
    """Coefficient sign after shifting by the appropriate branch root bound."""
    if s not in (-1, 1):
        raise ValueError("invalid boundary branch")
    c0 = 4*s*w[0] + 2*s*w[1]
    c1 = (2+4*s)*w[0] + (2+2*s)*w[1] + 2*w[2]
    c2 = 3*w[0] + 3*w[1] + 2*w[2]
    t = 2*floor + (6 if s == -1 else 3)
    shifted = (c0 + c1*t + c2*t*t, c1 + 2*c2*t, c2)
    if all(x == 0 for x in shifted):
        return 0
    if all(x >= 0 for x in shifted):
        return 1
    if all(x <= 0 for x in shifted):
        return -1
    raise Undecided(("geometry", w, shifted))


def real(vertex, floor, s=-1):
    top, bottom, *w = vertex
    return (sign(add(w, UNIT[bottom]), floor, s) > 0
            and sign(add(UNIT[top], neg(w)), floor, s) > 0)


def geq(affine, floor):
    """Decide slope*a+base >= 0 for every a>=floor, or refuse."""
    slope, base = affine
    value = slope*floor + base
    if slope >= 0 and value >= 0:
        return True
    if slope <= 0 and value < 0:
        return False
    raise Undecided(("range", affine, floor))


def seeds(floor, s=-1):
    out = set()
    for a in range(3):
        for b in range(a+1, 3):
            for top, top_start in ((a, (0, 0, 0)), (b, UNIT[a])):
                for bottom, bottom_start in ((b, (0, 0, 0)), (a, UNIT[b])):
                    vertex = (top, bottom, *add(bottom_start, neg(top_start)))
                    if real(vertex, floor, s):
                        out.add(vertex)
    return sorted(out)


def segment(letter, part, s=-1):
    """Child letter, constant prefix vector, affine y-prefix contribution."""
    child = (FIRST[letter], 2, LAST[letter])[part]
    prefix = UNIT[FIRST[letter]] if part else (0, 0, 0)
    return child, prefix, run(letter, s) if part == 2 else (0, 0)


def children(vertex, floor, s=-1):
    top, bottom, x, y, z = vertex
    if top == bottom and (x, y, z) == (0, 0, 0):
        return set()  # coincident overlaps are terminal in this graph
    out = set()
    base_xy = (x+y, x+y+2*z)
    base_z = (3*x+3*y+2*z, (4-s)*x+(4-2*s)*y+(2-2*s)*z)
    for top_part in range(3):
        top_child, top_prefix, top_affine = segment(top, top_part, s)
        for bottom_part in range(3):
            bottom_child, bottom_prefix, bottom_affine = segment(bottom, bottom_part, s)
            u = base_xy[0] + bottom_prefix[0] - top_prefix[0]
            v = base_xy[1] + bottom_prefix[1] - top_prefix[1]
            slope = base_z[0] + bottom_affine[0] - top_affine[0]
            base = base_z[1] + bottom_affine[1] - top_affine[1]
            lower = (-run(top,s)[0], 1-run(top,s)[1]) if top_part == 1 else (0, 0)
            upper = (run(bottom,s)[0], run(bottom,s)[1]-1) if bottom_part == 1 else (0, 0)
            bound = 2 + 2*(abs(u)+abs(v))
            if bound > 100:
                raise RuntimeError("COORDINATE_BUDGET_EXHAUSTED")
            for c in range(-bound, bound+1):
                child = (top_child, bottom_child, u, v, c)
                if not real(child, floor, s):
                    continue
                # m=c-(slope*a+base). Every integer in [lower,upper]
                # is realized by differences of actual segment positions.
                if (geq((-slope-lower[0], c-base-lower[1]), floor)
                        and geq((upper[0]+slope, upper[1]-c+base), floor)):
                    out.add(child)
    return out


def build(floor=4, cap=20000, s=-1):
    if s not in (-1, 1) or (s == 1 and floor < 1):
        raise ValueError("invalid branch or plus tail includes an empty run")
    if not 0 <= floor <= 64 or not 1 <= cap <= 20000:
        raise ValueError("outside declared threshold/state budget")
    roots = seeds(floor, s)
    queue = deque(roots)
    seen = set(roots)
    graph = {}
    while queue:
        if len(seen) > cap:
            raise RuntimeError("STATE_BUDGET_EXHAUSTED")
        vertex = queue.popleft()
        graph[vertex] = children(vertex, floor, s)
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


def check_exact_support(graph, a, s=-1):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from class_d_boundary_probe import labelled_support
    if graph != labelled_support(a, s):
        raise ValueError("labelled directed support differs")


def report(s=-1):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from class_d_boundary_probe import probe
    floor = 4 if s == -1 else 7
    graph = build(floor, s=s)
    depth = depths(graph)
    if set(depth) != set(graph):
        raise ValueError("symbolic target-free vertex")
    finite_prefix = [probe(s, a) for a in range(floor)]
    if any(row["missing"] for row in finite_prefix):
        raise ValueError("finite-prefix target-free vertex")
    for a in (floor, 8):
        check_exact_support(graph, a, s)
    vertices = sorted(graph)
    index = {v: i for i, v in enumerate(vertices)}
    return {
        "status": "INDEPENDENT_SYMBOLIC_REPLAY_COMPLETE",
        "authority": "independent-exact-integer-python-oracle",
        "canonical_execution": "NOT_RUN_LOCALLY",
        "canonical_replay": "kernel/class_d_boundary_certificate.mojo" if s == -1 else "kernel/class_d_plus_boundary_certificate.mojo",
        "scope": f"s={s}, b=0, all integer a>=0; closure candidate pending canonical receipt",
        "symbolic_floor": floor,
        "symbolic_vertices": len(vertices),
        "symbolic_directed_edges": sum(map(len, graph.values())),
        "max_half_depth": max(depth.values()),
        "full_support_crosschecks": [floor, 8],
        "finite_prefix": finite_prefix,
        "vertex_cap": 20000,
        "coordinate_candidate_cap": 100,
        "rng": "NONE",
        "vertices": vertices,
        "seeds": [index[v] for v in seeds(floor, s)],
        "adjacency": [sorted(index[w] for w in graph[v]) for v in vertices],
        "depths": [depth[v] for v in vertices],
    }


if __name__ == "__main__":
    if sys.argv[1:] not in ([], ["--plus"]):
        raise ValueError("usage: class_d_boundary_template.py [--plus]")
    print(json.dumps(report(1 if sys.argv[1:] else -1), indent=2))
