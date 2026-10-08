"""Certificate: boundary hitting on a whole line of catch-up-free substitutions.

docs/p1b-symbolic-line-2026-10-07.md (Theorem L), docs/p1-seed-strength-2026-10-08.md
§5 (Theorem L') and docs/p1b-boundary-hitting-progress-2026-10-08.md §4
(Theorem L''). A line is a family in Theorem E's normal form

    sigma_n(x) = x y^p s_x,   sigma_n(c) = c y^q s_c,   sigma_n(y) = t y^r s_y,

of class A, B, C or D (`class_ending`), with `p, q, r` affine in `n`; letters
`x = 0`, `c = 1`, `y = 2`, and `|det M| = 2` is required. Theorem L's line is
class B with p = 2n + 2, q = n, r = n + 1. The certificate has three parts:

1. `psc.symbolic_line.symbolic_line_graph` computes the swap-seed overlap
   graph for every `n >= q0` at once and certifies `q0`; every vertex of it
   must have an offset-zero descendant.
2. Every `n < q0` whose member is PIP is decided by the exact kernel
   (`build_seed_overlap_tables_screened`, `build_seed_overlap_graph_from_tables`,
   `first_left_aligned_depths`): every seed-reachable vertex must have an
   offset-zero descendant.
3. A cross-check, not part of the proof: at `q0` and `q0 + 5` the symbolic
   graph with `n` substituted must equal the exact graph, vertex for vertex.

A failure of any part raises. Usage: `mojo run -I . symbolic_line_certificate.mojo`
(Theorem L's line), `... SLOPE K BRANCH` (the class B line p = SLOPE n + K,
q = n, r = n + BRANCH), `... CLASS AP BP AQ BQ AR BR` (p = AP n + BP, ...,
CLASS one of A B C D), or `... lines` (every line in `certified_lines()`);
`pixi run symbolic-line-certificate` runs the first. Any other argument shape
raises. A listed line must also reproduce its pinned verdict;
`.github/workflows/class-b-lines-evidence.yml` runs every listed line, and
`tests/test_line_certificate_workflow.py` keeps its matrix equal to the list.
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
from a1_normal_form_census import C, CLASS_A, CLASS_B, CLASS_C, CLASS_D, X, Y, class_ending, class_member
from psc.symbolic_line import QX


# A line of Theorem E: class CLASS_A..CLASS_D with p, q, r affine in the line
# parameter n. Every member is in Theorem E's normal form, so Corollary E2 gives
# strong coincidence for every pair wherever |det M| = 2.
struct ClassLine(Copyable, Movable):
    var cls: Int
    var coef: List[Int]  # [a_p, b_p, a_q, b_q, a_r, b_r]: p = a_p n + b_p, ...

    def __init__(out self, cls: Int, coef: List[Int]) raises:
        if cls < CLASS_A or cls > CLASS_D or len(coef) != 6:
            raise Error("a class line is a class A..D and six affine coefficients")
        self.cls = cls
        self.coef = coef.copy()

    def run(self, i: Int, n: Int) -> Int:
        """The y-run of letter i (x, c, y) = (p, q, r) at parameter n."""
        return self.coef[2 * i] * n + self.coef[2 * i + 1]

    def admissible(self, n: Int) -> Bool:
        """Inside the class's normal form (p, q, r >= 0) and, in classes A-C,
        Lemma P1's necessary PIP condition p > q."""
        var p = self.run(0, n)
        var q = self.run(1, n)
        return n >= 0 and p >= 0 and q >= 0 and self.run(2, n) >= 0 and (self.cls == CLASS_D or p > q)

    def member(self, n: Int) raises -> List[List[Int]]:
        return class_member(self.cls, self.run(0, n), self.run(1, n), self.run(2, n))

    def line(self) raises -> Line:
        var e = class_ending(self.cls)  # (s_x, s_c, t, s_y)
        var runs = List[QX]()
        for i in range(3):
            runs.append(qx_affine(self.coef[2 * i + 1], self.coef[2 * i]))
        return Line([X, C, e[2]], [e[0], e[1], e[3]], runs, Y)

    def key(self) -> List[Int]:
        var out = List[Int]([self.cls])
        out.extend(self.coef.copy())
        return out^

    def describe(self) -> String:
        var out = String("class ") + String(chr(ord("A") + self.cls)) + " line"
        var names = ["p", "q", "r"]
        for i in range(3):
            out += " " + names[i] + " = " + String(self.coef[2 * i]) + "n + " + String(self.coef[2 * i + 1])
        return out^


# A line of class B: p = slope q + k, r = q + branch (|r - q| = 1 is Lemma P1's
# determinant-2 condition). The default is Theorem L's line.
def class_b(slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> ClassLine:
    return ClassLine(CLASS_B, [slope, k, 1, 0, 1, branch])


def class_b_line(slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> Line:
    return class_b(slope, k, branch).line()


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


def certify(spec: ClassLine) raises -> LineVerdict:
    """Every PIP member of the line has every seed-reachable overlap hitting
    offset zero, and `|det M| = 2` (the hypothesis of Corollary E2)."""
    var out = LineVerdict()
    var g = symbolic_line_graph(spec.line())
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
    if abs(Mat3(substitution_incidence(spec.member(out.q0))).det()) != 2:
        raise Error("the line's determinant is not +-2, so Corollary E2 does not apply")
    for q in range(out.q0):
        if not spec.admissible(q):
            out.finite_outside += 1
            continue
        var sigma = spec.member(q)
        var m = Mat3(substitution_incidence(sigma))
        if not screen.is_pip(m):
            out.finite_non_pip += 1
            continue
        if abs(m.det()) != 2:
            raise Error("a PIP member has |det M| != 2")
        _ = exact_hits(sigma)
        out.finite_members += 1
    for q in [out.q0, out.q0 + 5]:
        if not same_set(symbolic_vertex_keys(g, q), exact_vertex_keys(spec.member(q))):
            raise Error("cross-check: the symbolic graph differs from the exact graph")
    return out^


def certify_class_b_line(slope: Int = 2, k: Int = 2, branch: Int = 1) raises -> LineVerdict:
    return certify(class_b(slope, k, branch))


# The lines certified so far: class, then a_p, b_p, a_q, b_q, a_r, b_r
# (p = a_p n + b_p, ...), then the pinned verdict: q0, symbolic vertices, PIP
# members below q0, non-PIP members below q0, parameters below q0 outside the
# admissible cone. Class B rows are Theorem L (first) and Theorem L' of
# docs/p1-seed-strength-2026-10-08.md; rows of classes A, C, D are Theorem L''
# of docs/p1b-boundary-hitting-progress-2026-10-08.md.
comptime PIN_FIELDS = 12


def certified_lines() -> List[List[Int]]:
    return [
        [CLASS_B, 2, 2, 1, 0, 1, 1, 52, 119, 52, 0, 0],
        [CLASS_B, 1, 1, 1, 0, 1, 1, 14, 121, 14, 0, 0],
        [CLASS_B, 1, 2, 1, 0, 1, 1, 11, 77, 11, 0, 0],
        [CLASS_B, 1, 3, 1, 0, 1, 1, 22, 79, 22, 0, 0],
        [CLASS_B, 1, 1, 1, 0, 1, -1, 20, 166, 19, 0, 1],
        [CLASS_B, 1, 2, 1, 0, 1, -1, 16, 144, 14, 1, 1],
        [CLASS_B, 1, 3, 1, 0, 1, -1, 32, 131, 30, 1, 1],
        [CLASS_B, 2, 0, 1, 0, 1, 1, 20, 76, 19, 0, 1],
        [CLASS_B, 2, 1, 1, 0, 1, 1, 17, 84, 17, 0, 0],
        [CLASS_B, 2, 3, 1, 0, 1, 1, 14, 123, 14, 0, 0],
        [CLASS_B, 2, 4, 1, 0, 1, 1, 15, 123, 15, 0, 0],
        [CLASS_B, 2, 0, 1, 0, 1, -1, 34, 124, 33, 0, 1],
        [CLASS_B, 2, 1, 1, 0, 1, -1, 87, 274, 85, 1, 1],
        [CLASS_B, 2, 2, 1, 0, 1, -1, 107, 255, 104, 2, 1],
        [CLASS_B, 2, 3, 1, 0, 1, -1, 128, 248, 124, 3, 1],
        [CLASS_A, 2, 0, 1, 0, 1, -1, 39, 281, 38, 0, 1],
        [CLASS_A, 2, 0, 1, 0, 1, 1, 20, 210, 19, 0, 1],
        [CLASS_A, 2, 1, 1, 0, 1, -1, 87, 365, 85, 1, 1],
        [CLASS_A, 2, 1, 1, 0, 1, 1, 19, 194, 19, 0, 0],
        [CLASS_A, 2, 2, 1, 0, 1, -1, 107, 325, 104, 2, 1],
        [CLASS_A, 2, 2, 1, 0, 1, 1, 52, 230, 52, 0, 0],
        [CLASS_A, 2, 3, 1, 0, 1, -1, 128, 303, 124, 3, 1],
        [CLASS_A, 2, 3, 1, 0, 1, 1, 14, 260, 14, 0, 0],
        [CLASS_C, 1, 1, 1, 0, 1, -2, 36, 279, 33, 1, 2],
        [CLASS_C, 1, 1, 1, 0, 1, 0, 17, 169, 17, 0, 0],
        [CLASS_C, 1, 2, 1, 0, 1, -3, 37, 238, 32, 2, 3],
        [CLASS_C, 1, 2, 1, 0, 1, -1, 23, 182, 22, 0, 1],
        [CLASS_C, 1, 3, 1, 0, 1, -4, 39, 229, 32, 3, 4],
        [CLASS_C, 1, 3, 1, 0, 1, -2, 36, 188, 34, 0, 2],
        [CLASS_D, 1, -1, 1, 0, 1, -1, 22, 150, 19, 2, 1],
        [CLASS_D, 1, -1, 1, 0, 1, 0, 17, 128, 15, 1, 1],
        [CLASS_D, 1, -1, 1, 0, 1, 1, 26, 111, 23, 2, 1],
        [CLASS_D, 1, -1, 1, 0, 1, 2, 38, 105, 34, 3, 1],
        [CLASS_D, 1, -1, 1, 0, 1, 3, 43, 105, 38, 4, 1],
        [CLASS_D, 1, -1, 1, 0, 1, 4, 97, 105, 91, 5, 1],
        [CLASS_D, 1, -1, 1, 0, 2, -3, 14, 105, 11, 1, 2],
        [CLASS_D, 1, -1, 1, 0, 2, -2, 12, 113, 10, 1, 1],
        [CLASS_D, 1, 1, 1, 0, 1, -1, 24, 250, 23, 0, 1],
        [CLASS_D, 1, 1, 1, 0, 1, 0, 19, 246, 19, 0, 0],
        [CLASS_D, 1, 1, 1, 0, 1, 1, 21, 181, 21, 0, 0],
        [CLASS_D, 1, 1, 1, 0, 1, 2, 22, 132, 22, 0, 0],
        [CLASS_D, 1, 1, 1, 0, 1, 3, 18, 97, 17, 1, 0],
        [CLASS_D, 1, 1, 1, 0, 1, 4, 49, 93, 47, 2, 0],
        [CLASS_D, 1, 1, 1, 0, 2, -1, 22, 93, 21, 0, 1],
        [CLASS_D, 1, 1, 1, 0, 2, 0, 15, 93, 15, 0, 0],
        [CLASS_D, 1, 1, 1, 0, 2, 1, 14, 113, 14, 0, 0],
        [CLASS_D, 1, 1, 1, 0, 2, 2, 10, 193, 10, 0, 0],
    ]


def part(xs: List[Int], lo: Int, hi: Int) -> List[Int]:
    var out = List[Int]()
    for i in range(lo, hi):
        out.append(xs[i])
    return out^


def spec_of(row: List[Int]) raises -> ClassLine:
    return ClassLine(row[0], part(row, 1, 7))


def pinned(spec: ClassLine) -> List[Int]:
    """The pinned verdict of a listed line, or an empty list."""
    var lines = certified_lines()
    for i in range(len(lines)):
        if part(lines[i], 0, 7) == spec.key():
            return lines[i].copy()
    return List[Int]()


def pinned(slope: Int, k: Int, branch: Int) raises -> List[Int]:
    return pinned(class_b(slope, k, branch))


def check_pinned(v: LineVerdict, pin: List[Int]) raises:
    """A listed line must reproduce its pinned verdict exactly."""
    if len(pin) != PIN_FIELDS or List[Int]([v.q0, v.symbolic_vertices, v.finite_members, v.finite_non_pip, v.finite_outside]) != part(pin, 7, PIN_FIELDS):
        raise Error("the line's verdict differs from its pinned verdict in certified_lines()")


def report(spec: ClassLine) raises:
    var v = certify(spec)
    print(spec.describe(), "(Theorem E normal form):")
    print("  symbolic graph for every n >=", v.q0, ":", v.symbolic_vertices, "vertices, all with an offset-zero descendant;", v.queries, "certified sign reads")
    print("  n <", v.q0, ":", v.finite_members, "PIP members decided exactly, all hitting;", v.finite_non_pip, "not PIP;", v.finite_outside, "outside the admissible cone")
    print("  cross-check at q0 and q0 + 5: symbolic graph = exact graph")
    var pin = pinned(spec)
    if len(pin) > 0:
        check_pinned(v, pin)
        print("  pinned verdict reproduced")


def class_of(name: String) raises -> Int:
    for c in range(CLASS_A, CLASS_D + 1):
        if name == String(chr(ord("A") + c)):
            return c
    raise Error("a class is one of A, B, C, D")


def mode_of(args: List[String]) raises -> String:
    """`default` (no argument), `line` (three integers: a class B line),
    `class` (a class letter and six integers) or `lines`; any other shape
    raises, so a typo never silently certifies the default line instead."""
    if len(args) == 0:
        return "default"
    if len(args) == 1 and args[0] == "lines":
        return "lines"
    if len(args) == 3:
        for i in range(3):
            _ = Int(args[i])  # raises unless an integer
        return "line"
    if len(args) == 7:
        _ = class_of(args[0])
        for i in range(1, 7):
            _ = Int(args[i])
        return "class"
    raise Error("usage: symbolic_line_certificate.mojo [SLOPE K BRANCH | CLASS AP BP AQ BQ AR BR | lines]")


def spec_from(args: List[String], mode: String) raises -> ClassLine:
    if mode == "line":
        return class_b(Int(args[0]), Int(args[1]), Int(args[2]))
    var coef = List[Int]()
    for i in range(1, 7):
        coef.append(Int(args[i]))
    return ClassLine(class_of(args[0]), coef)


def main() raises:
    var argv_ = argv()
    var args = List[String]()
    for i in range(1, len(argv_)):
        args.append(String(argv_[i]))
    var mode = mode_of(args)
    if mode == "lines":
        var lines = certified_lines()
        for i in range(len(lines)):
            report(spec_of(lines[i]))
        print("certified lines:", len(lines))
        return
    report(class_b() if mode == "default" else spec_from(args, mode))
