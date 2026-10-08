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

A failure of any part raises. Usage: `mojo run -I . symbolic_line_certificate.mojo`
(Theorem L's line), `... symbolic_line_certificate.mojo SLOPE K BRANCH` (the class B
line p = SLOPE q + K, r = q + BRANCH), or `... lines` (every line in
`certified_lines()`); `pixi run symbolic-line-certificate` runs the first.
"""

from std.collections import Dict
from std.sys import argv
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


# A line of class B: p = slope q + k, r = q + branch (|r - q| = 1 is Lemma P1's
# determinant-2 condition). The default is Theorem L's line.
def class_b_line(slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> Line:
    return Line([0, 1, 1], [0, 0, 0], [qx_affine(k, slope), qx_affine(0, 1), qx_affine(branch, 1)], 2)


def class_b_member(q: Int, slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> List[List[Int]]:
    return class_member(CLASS_B, slope * q + k, q, q + branch)


def in_class_b(q: Int, slope: Int, k: Int, branch: Int) -> Bool:
    """Theorem E's class B needs `p > q >= 0` and `r >= 0`."""
    return q >= 0 and slope * q + k > q and q + branch >= 0


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
    var finite_outside: Int

    def __init__(out self):
        self.q0 = -1
        self.symbolic_vertices = 0
        self.queries = 0
        self.finite_members = 0
        self.finite_non_pip = 0
        self.finite_outside = 0


def certify_class_b_line(slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> LineVerdict:
    """Every PIP member of the line has every seed-reachable overlap hitting
    offset zero, and `|det M| = 2` (the hypothesis of Corollary E2)."""
    var out = LineVerdict()
    var g = symbolic_line_graph(class_b_line(slope, k, branch))
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
    if abs(Mat3(substitution_incidence(class_b_member(out.q0, slope, k, branch))).det()) != 2:
        raise Error("the line's determinant is not +-2, so Corollary E2 does not apply")
    for q in range(out.q0):
        if not in_class_b(q, slope, k, branch):
            out.finite_outside += 1
            continue
        var sigma = class_b_member(q, slope, k, branch)
        var m = Mat3(substitution_incidence(sigma))
        if not screen.is_pip(m):
            out.finite_non_pip += 1
            continue
        if abs(m.det()) != 2:
            raise Error("a PIP member has |det M| != 2")
        _ = exact_hits(sigma)
        out.finite_members += 1
    for q in [out.q0, out.q0 + 5]:
        if not same_set(symbolic_vertex_keys(g, q), exact_vertex_keys(class_b_member(q, slope, k, branch))):
            raise Error("cross-check: the symbolic graph differs from the exact graph")
    return out^


# The class B lines certified so far, as (slope, k, branch): p = slope q + k,
# r = q + branch. The first is Theorem L; the others are Theorem L' of
# docs/p1-seed-strength-2026-10-08.md.
def certified_lines() -> List[List[Int]]:
    return [
        [2, 2, 1],
        [1, 1, 1], [1, 2, 1], [1, 3, 1], [1, 1, -1], [1, 2, -1], [1, 3, -1],
        [2, 0, 1], [2, 1, 1], [2, 3, 1], [2, 4, 1], [2, 0, -1], [2, 1, -1], [2, 2, -1],
    ]


def report(slope: Int, k: Int, branch: Int) raises:
    var v = certify_class_b_line(slope, k, branch)
    print("class B line p =", slope, "q +", k, " r = q +", branch, "(x -> x y^p x, c -> c y^q x, y -> c y^r x):")
    print("  symbolic graph for every q >=", v.q0, ":", v.symbolic_vertices, "vertices, all with an offset-zero descendant;", v.queries, "certified sign reads")
    print("  q <", v.q0, ":", v.finite_members, "PIP members decided exactly, all hitting;", v.finite_non_pip, "not PIP;", v.finite_outside, "outside class B")
    print("  cross-check at q0 and q0 + 5: symbolic graph = exact graph")


def main() raises:
    var args = argv()
    if len(args) == 4:
        report(Int(String(args[1])), Int(String(args[2])), Int(String(args[3])))
        return
    if len(args) == 2 and String(args[1]) == "lines":
        var lines = certified_lines()
        for i in range(len(lines)):
            report(lines[i][0], lines[i][1], lines[i][2])
        print("certified class B lines:", len(lines))
        return
    var v = certify_class_b_line()
    print("class B line x -> x y^(2q+2) x, c -> c y^q x, y -> c y^(q+1) x")
    print("  symbolic graph for every q >=", v.q0, ":", v.symbolic_vertices, "vertices, all with an offset-zero descendant;", v.queries, "certified sign reads")
    print("  q <", v.q0, ":", v.finite_members, "PIP members decided exactly, all hitting;", v.finite_non_pip, "not PIP")
    print("  cross-check at q0 and q0 + 5: symbolic graph = exact graph")
