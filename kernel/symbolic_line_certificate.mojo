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
`certified_lines()`); `pixi run symbolic-line-certificate` runs the first. Any
other argument shape raises. A listed line must also reproduce its pinned
verdict; `.github/workflows/class-b-lines-evidence.yml` runs every listed line.
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


# A class B family: p = p0 + pt t + pd d, q = q0 + qt t + qd d, r = q + branch, as
# [p0, pt, pd, q0, qt, qd, branch] (|r - q| = 1 is Lemma P1's determinant-2
# condition). A line has pd = qd = 0; the lines of Theorems L and L' have q = t.
def slope_family(slope: Int, k: Int, branch: Int) -> List[Int]:
    """The line p = slope q + k, r = q + branch."""
    return [k, slope, 0, 0, 1, 0, branch]


def family_line(f: List[Int]) raises -> Line:
    var q = qx_affine(f[3], f[4], f[5])
    return Line([0, 1, 1], [0, 0, 0], [qx_affine(f[0], f[1], f[2]), q.copy(), qx_affine(f[3] + f[6], f[4], f[5])], 2)


def family_pqr(f: List[Int], t: Int, d: Int = 0) -> List[Int]:
    var q = f[3] + f[4] * t + f[5] * d
    return [f[0] + f[1] * t + f[2] * d, q, q + f[6]]


def in_class_b_pqr(pqr: List[Int]) -> Bool:
    """Theorem E's class B needs `p > q >= 0` and `r >= 0`."""
    return pqr[1] >= 0 and pqr[0] > pqr[1] and pqr[2] >= 0


def family_member(f: List[Int], t: Int, d: Int = 0) raises -> List[List[Int]]:
    var pqr = family_pqr(f, t, d)
    return class_member(CLASS_B, pqr[0], pqr[1], pqr[2])


# The default is Theorem L's line.
def class_b_line(slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> Line:
    return family_line(slope_family(slope, k, branch))


def class_b_member(q: Int, slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> List[List[Int]]:
    return family_member(slope_family(slope, k, branch), q)


def in_class_b(q: Int, slope: Int, k: Int, branch: Int) -> Bool:
    return in_class_b_pqr(family_pqr(slope_family(slope, k, branch), q))


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


def symbolic_vertex_keys(g: SymbolicLineGraph, q: Int, d: Int = 0) raises -> List[String]:
    var out = List[String]()
    for i in range(g.size()):
        ref v = g.vertices[i]
        var key = String(v.top) + "|" + String(v.bottom) + "|"
        for k in range(3):
            var x = qx_at(v.w[k], q, d)
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


def all_hitting(g: SymbolicLineGraph) raises:
    if not g.pip:
        raise Error("the family's PIP property was not certified")
    var good = offset_zero_reachable(g)
    for i in range(len(good)):
        if not good[i]:
            raise Error("a symbolic seed-reachable vertex has no offset-zero descendant")


def require_det_two(sigma: List[List[Int]]) raises:
    if abs(Mat3(substitution_incidence(sigma)).det()) != 2:
        raise Error("|det M| != 2, so Corollary E2 does not apply")


def certify_family_line(f: List[Int]) raises -> LineVerdict:
    """Every PIP member of the line `f` (parameter `t >= 0`) has every
    seed-reachable overlap hitting offset zero, and `|det M| = 2` (the
    hypothesis of Corollary E2)."""
    if f[2] != 0 or f[5] != 0:
        raise Error("a line family has no second parameter")
    var out = LineVerdict()
    var g = symbolic_line_graph(family_line(f))
    all_hitting(g)
    out.symbolic_vertices = g.size()
    out.queries = g.queries
    out.q0 = g_first_integer_above(g)
    require_det_two(family_member(f, out.q0))
    var screen = CubicScreen()
    for t in range(out.q0):
        if not in_class_b_pqr(family_pqr(f, t)):
            out.finite_outside += 1
            continue
        var sigma = family_member(f, t)
        if not screen.is_pip(Mat3(substitution_incidence(sigma))):
            out.finite_non_pip += 1
            continue
        require_det_two(sigma)
        _ = exact_hits(sigma)
        out.finite_members += 1
    for t in [out.q0, out.q0 + 5]:
        if not same_set(symbolic_vertex_keys(g, t), exact_vertex_keys(family_member(f, t))):
            raise Error("cross-check: the symbolic graph differs from the exact graph")
    return out^


def g_first_integer_above(g: SymbolicLineGraph) -> Int:
    var n = 0
    while not g.threshold.lt(q_int(n)):
        n += 1
    return n


def certify_class_b_line(slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> LineVerdict:
    return certify_family_line(slope_family(slope, k, branch))


# The class B lines certified so far, as (slope, k, branch): p = slope q + k,
# r = q + branch. The first is Theorem L; the others are Theorem L' of
# docs/p1-seed-strength-2026-10-08.md.
# slope, k, branch, then the pinned verdict: q0, symbolic vertices, PIP members
# below q0, non-PIP members below q0, parameters below q0 outside class B.
def certified_lines() -> List[List[Int]]:
    return [
        [2, 2, 1, 52, 119, 52, 0, 0],
        [1, 1, 1, 14, 121, 14, 0, 0],
        [1, 2, 1, 11, 77, 11, 0, 0],
        [1, 3, 1, 22, 79, 22, 0, 0],
        [1, 1, -1, 20, 166, 19, 0, 1],
        [1, 2, -1, 16, 144, 14, 1, 1],
        [1, 3, -1, 32, 131, 30, 1, 1],
        [2, 0, 1, 20, 76, 19, 0, 1],
        [2, 1, 1, 17, 84, 17, 0, 0],
        [2, 3, 1, 14, 123, 14, 0, 0],
        [2, 4, 1, 15, 123, 15, 0, 0],
        [2, 0, -1, 34, 124, 33, 0, 1],
        [2, 1, -1, 87, 274, 85, 1, 1],
        [2, 2, -1, 107, 255, 104, 2, 1],
        [2, 3, -1, 128, 248, 124, 3, 1],
    ]


def pinned(slope: Int, k: Int, branch: Int) -> List[Int]:
    """The pinned verdict of a listed line, or an empty list."""
    var lines = certified_lines()
    for i in range(len(lines)):
        if lines[i][0] == slope and lines[i][1] == k and lines[i][2] == branch:
            return lines[i].copy()
    return List[Int]()


def check_pinned(v: LineVerdict, pin: List[Int]) raises:
    """A listed line must reproduce its pinned verdict exactly."""
    if (
        v.q0 != pin[3]
        or v.symbolic_vertices != pin[4]
        or v.finite_members != pin[5]
        or v.finite_non_pip != pin[6]
        or v.finite_outside != pin[7]
    ):
        raise Error("the line's verdict differs from its pinned verdict in certified_lines()")


def report(slope: Int, k: Int, branch: Int) raises:
    var v = certify_class_b_line(slope, k, branch)
    print("class B line p =", slope, "q +", k, " r = q +", branch, "(x -> x y^p x, c -> c y^q x, y -> c y^r x):")
    print("  symbolic graph for every q >=", v.q0, ":", v.symbolic_vertices, "vertices, all with an offset-zero descendant;", v.queries, "certified sign reads")
    print("  q <", v.q0, ":", v.finite_members, "PIP members decided exactly, all hitting;", v.finite_non_pip, "not PIP;", v.finite_outside, "outside class B")
    print("  cross-check at q0 and q0 + 5: symbolic graph = exact graph")
    var pin = pinned(slope, k, branch)
    if len(pin) > 0:
        check_pinned(v, pin)
        print("  pinned verdict reproduced")


def mode_of(args: List[String]) raises -> String:
    """`default` (no argument), `line` (three integers) or `lines`; any other
    shape raises, so a typo never silently certifies the default line instead."""
    if len(args) == 0:
        return "default"
    if len(args) == 1 and args[0] == "lines":
        return "lines"
    if len(args) == 3:
        for i in range(3):
            _ = Int(args[i])  # raises unless an integer
        return "line"
    raise Error("usage: symbolic_line_certificate.mojo [SLOPE K BRANCH | lines]")


def main() raises:
    var argv_ = argv()
    var args = List[String]()
    for i in range(1, len(argv_)):
        args.append(String(argv_[i]))
    var mode = mode_of(args)
    if mode == "line":
        report(Int(args[0]), Int(args[1]), Int(args[2]))
        return
    if mode == "lines":
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
