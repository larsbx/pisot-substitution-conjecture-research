"""Certificate: boundary hitting on a whole line of catch-up-free substitutions.

docs/p1b-symbolic-line-2026-10-07.md. The line is Theorem E's class B with

    sigma_q(x) = x y^(2q+2) x,   sigma_q(c) = c y^q x,   sigma_q(y) = c y^(q+1) x,

letters `x = 0`, `c = 1`, `y = 2`, `|det M| = 2`. The certificate has three parts:

1. `psc.symbolic_line.symbolic_line_graph` computes the swap-seed overlap
   graph for every `q >= q0` at once and certifies `q0`; every vertex of it
   must have an offset-zero descendant.
2. Every `q < q0` whose member is PIP is decided by the exact kernel
   (`build_seed_overlap_tables_screened`, `build_seed_overlap_graph_from_tables`,
   `first_left_aligned_depths`): every seed-reachable vertex must have an
   offset-zero descendant.
3. A cross-check, not part of the proof: at `q0` and `q0 + 5` the symbolic
   graph with `q` substituted must equal the exact graph, vertex for vertex.

A failure of any part raises. Usage: `mojo run -I . symbolic_line_certificate.mojo`,
or `pixi run symbolic-line-certificate`.
"""

from std.collections import Dict
from finite_linear_algebra.mat3 import Mat3
from finite_linear_algebra.scalar import q_int
from psc.bpa import substitution_incidence
from psc.exact import q_string
from psc.overlap_seed_patch import (
    build_seed_overlap_graph_from_tables,
    build_seed_overlap_tables_screened,
    first_left_aligned_depths,
)
from psc.pisot import CubicScreen
from psc.symbolic_line import Line, SymbolicLineGraph, offset_zero_reachable, qx_affine, qx_at, symbolic_line_graph
from psc.vertex_coincidence import length_matrix, offset_vector
from a1_normal_form_census import CLASS_B, class_member


def class_b_line() raises -> Line:
    return Line([0, 1, 1], [0, 0, 0], [qx_affine(2, 2), qx_affine(0, 1), qx_affine(1, 1)], 2)


def class_b_member(q: Int) raises -> List[List[Int]]:
    return class_member(CLASS_B, 2 * q + 2, q, q + 1)


def exact_hits(sigma: List[List[Int]]) raises -> Int:
    """Vertices of the exact seed-reachable graph, raising unless all have an
    offset-zero descendant."""
    var g = build_seed_overlap_graph_from_tables(build_seed_overlap_tables_screened(sigma), 200000)
    if g.capped:
        raise Error("exact seed graph capped: an exhausted budget, not a verdict")
    var depths = first_left_aligned_depths(g)
    for i in range(len(depths)):
        if depths[i] < 0:
            raise Error("a seed-reachable vertex has no offset-zero descendant")
    return g.size()


def exact_vertex_keys(sigma: List[List[Int]]) raises -> List[String]:
    var tables = build_seed_overlap_tables_screened(sigma)
    var g = build_seed_overlap_graph_from_tables(tables, 200000)
    var lm = length_matrix(tables)
    var out = List[String]()
    for i in range(g.size()):
        var s = g.states[i]
        var w = offset_vector(lm, s.shift)
        out.append(String(s.top) + "|" + String(s.bottom) + "|" + String(w[0]) + "," + String(w[1]) + "," + String(w[2]))
    return out^


def symbolic_vertex_keys(g: SymbolicLineGraph, q: Int) raises -> List[String]:
    var out = List[String]()
    for i in range(g.size()):
        ref v = g.vertices[i]
        var key = String(v.top) + "|" + String(v.bottom) + "|"
        for k in range(3):
            var x = qx_at(v.w[k], q)
            key += q_string(x) + ("," if k < 2 else "")
        out.append(key^)
    return out^


def same_set(a: List[String], b: List[String]) -> Bool:
    if len(a) != len(b):
        return False
    var seen = Dict[String, Int]()
    for i in range(len(a)):
        seen[a[i]] = 1
    for i in range(len(b)):
        if b[i] not in seen:
            return False
    return True


struct LineVerdict(Copyable, Movable):
    var q0: Int
    var symbolic_vertices: Int
    var queries: Int
    var finite_members: Int
    var finite_non_pip: Int

    def __init__(out self):
        self.q0 = -1
        self.symbolic_vertices = 0
        self.queries = 0
        self.finite_members = 0
        self.finite_non_pip = 0


def certify_class_b_line() raises -> LineVerdict:
    var out = LineVerdict()
    var g = symbolic_line_graph(class_b_line())
    if not g.pip:
        raise Error("the line's PIP property was not certified")
    var good = offset_zero_reachable(g)
    for i in range(len(good)):
        if not good[i]:
            raise Error("a symbolic seed-reachable vertex has no offset-zero descendant")
    out.symbolic_vertices = g.size()
    out.queries = g.queries
    var n = 0
    while not g.threshold.lt(q_int(n)):
        n += 1
    out.q0 = n
    var screen = CubicScreen()
    for q in range(out.q0):
        var sigma = class_b_member(q)
        if not screen.is_pip(Mat3(substitution_incidence(sigma))):
            out.finite_non_pip += 1
            continue
        _ = exact_hits(sigma)
        out.finite_members += 1
    for q in [out.q0, out.q0 + 5]:
        if not same_set(symbolic_vertex_keys(g, q), exact_vertex_keys(class_b_member(q))):
            raise Error("cross-check: the symbolic graph differs from the exact graph")
    return out^


def main() raises:
    var v = certify_class_b_line()
    print("class B line x -> x y^(2q+2) x, c -> c y^q x, y -> c y^(q+1) x")
    print("  symbolic graph for every q >=", v.q0, ":", v.symbolic_vertices, "vertices, all with an offset-zero descendant;", v.queries, "certified sign reads")
    print("  q <", v.q0, ":", v.finite_members, "PIP members decided exactly, all hitting;", v.finite_non_pip, "not PIP")
    print("  cross-check at q0 and q0 + 5: symbolic graph = exact graph")
