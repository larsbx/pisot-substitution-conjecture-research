"""Bounded replay of the two residual class-D b=0 families; no universal verdict."""
from psc.overlap_seed_patch import first_left_aligned_depths, build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables
from psc.vertex_coincidence import length_matrix, offset_vector


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
    # Boundary images exceed the matrix-level validator's audited length six.
    # The existing coefficient screen checks primitivity, irreducibility and
    # Pisot exactly, retaining checked arithmetic and its own entry bound.
    var tables = build_seed_overlap_tables_screened(boundary_member(s, a))
    var graph = build_seed_overlap_graph_from_tables(tables, max_states)
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


# Two actual support changes on s=-1, between a=2 and a=3. Labels are
# (top,bottom,w0,w1,w2), with canonical letters x=0,c=1,y=2.
def boundary_edge_flags(a: Int, max_states: Int = 20000) raises -> List[Bool]:
    if max_states < 1 or max_states > 20000:
        raise Error("boundary state cap outside 1..20000")
    var tables = build_seed_overlap_tables_screened(boundary_member(-1, a))
    var graph = build_seed_overlap_graph_from_tables(tables, max_states)
    if graph.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no support comparison")
    var lengths = length_matrix(tables)
    var parents: List[List[Int]] = [[0,0,0,0,1], [1,0,-1,1,1]]
    var children: List[List[Int]] = [[2,2,0,2,-3], [2,2,1,1,-3]]
    var found: List[Bool] = [False, False]
    var present: List[Bool] = [False, False]
    for i in range(graph.size()):
        var v = graph.states[i]
        var w = offset_vector(lengths, v.shift)
        for k in range(2):
            if v.top != parents[k][0] or v.bottom != parents[k][1]:
                continue
            if w != List[Int]([parents[k][2],parents[k][3],parents[k][4]]):
                continue
            found[k] = True
            for j in graph.adj[i]:
                var c = graph.states[j]
                if c.top != children[k][0] or c.bottom != children[k][1]:
                    continue
                var cw = offset_vector(lengths, c.shift)
                if cw == List[Int]([children[k][2],children[k][3],children[k][4]]):
                    present[k] = True
    if not found[0] or not found[1]:
        raise Error("support witness parent absent; no comparison")
    return present^
