"""Certificate: boundary hitting on the wedge q < p < 2q of class B, both branches.

docs/p1c-symbolic-wedge-2026-10-08.md. Class B is

    sigma(x) = x y^p x,   sigma(c) = c y^q x,   sigma(y) = c y^r x,   r = q + branch,

and the wedge is `q < p < 2q`, i.e. `s = p - q >= 1` and `d = 2q - p >= 1`. It is
cut into two cones and finitely many lines:

- cone A, `s >= d`: parameters `(e, d)` with `s = d + e`, so `q = e + 2d` and
  `p = 2e + 3d`;
- cone B, `s < d`: parameters `(s, e)` with `d = s + e`, so `q = 2s + e` and
  `p = 3s + e`.

`psc.symbolic_line` certifies each cone on a quadrant `{first >= s0, second >=
d0}` of its parameters (`symbolic_line_graph` on a two-parameter `Line`). The
rest of the wedge lies on the lines `wedge_boundary` lists (the strips below
either threshold), and each of those is certified as a line by
`certify_family_line` of `symbolic_line_certificate`, symbolic part and finite
part. A cone's verdict is cross-checked against the exact kernel, vertex for
vertex, at four parameter points; this is not part of the proof.

Usage: `mojo run -I . symbolic_wedge_certificate.mojo cone BRANCH WHICH` (WHICH
`0` for cone A, `1` for cone B), `... boundary BRANCH PART PARTS` (the boundary
lines with index `PART` mod `PARTS`), or `... wedge BRANCH` (everything, in
sequence). Any other argument shape raises. Every verdict must reproduce its pin
in `wedge_pins()` or `boundary_pins()`; the boundary lines are derived from the
pinned cone thresholds, so the cone jobs and the boundary jobs of
`.github/workflows/class-b-wedge-evidence.yml` together certify the wedge.
"""

from std.sys import argv
from psc.symbolic_line import Eventual, symbolic_line_graph
from symbolic_line_certificate import (
    LineVerdict,
    all_hitting,
    certify_family_line,
    exact_vertex_keys,
    family_line,
    family_member,
    family_pqr,
    in_class_b_pqr,
    require_det_two,
    same_set,
    slope_family,
    symbolic_vertex_keys,
)


def cone_family(branch: Int, which: Int) raises -> List[Int]:
    """Cone A (`which = 0`) in `(e, d)`, cone B (`which = 1`) in `(s, e)`."""
    if which == 0:
        return [0, 2, 3, 0, 1, 2, branch]
    if which == 1:
        return [0, 3, 1, 0, 2, 1, branch]
    raise Error("a wedge has cones 0 and 1")


struct ConeVerdict(Copyable, Movable):
    var s0: Int  # the first parameter is >= s0
    var d0: Int  # the second parameter is >= d0
    var symbolic_vertices: Int
    var queries: Int

    def __init__(out self):
        self.s0 = -1
        self.d0 = -1
        self.symbolic_vertices = 0
        self.queries = 0


def certify_cone(branch: Int, which: Int) raises -> ConeVerdict:
    """Every member of the cone's quadrant is PIP with `|det M| = 2`, and every
    overlap reachable from its swap seeds has an offset-zero descendant."""
    var f = cone_family(branch, which)
    var g = symbolic_line_graph(family_line(f))
    all_hitting(g)
    var ev = Eventual()
    ev.threshold = g.threshold.copy()
    ev.d_threshold = g.d_threshold.copy()
    var out = ConeVerdict()
    out.s0 = ev.first_integer_above()
    out.d0 = ev.first_integer_above_d()
    out.symbolic_vertices = g.size()
    out.queries = g.queries
    require_det_two(family_member(f, out.s0, out.d0))
    for k in range(4):
        var t = out.s0 + (5 if k % 2 == 1 else 0)
        var d = out.d0 + (5 if k >= 2 else 0)
        if not in_class_b_pqr(family_pqr(f, t, d)):
            raise Error("a cone point lies outside class B")
        if not same_set(symbolic_vertex_keys(g, t, d), exact_vertex_keys(family_member(f, t, d))):
            raise Error("cross-check: the symbolic cone graph differs from the exact graph")
    return out^


def wedge_boundary(branch: Int, a_s0: Int, a_d0: Int, b_s0: Int, b_d0: Int) -> List[List[Int]]:
    """The lines covering the wedge outside the two quadrants:

    - cone A with `e < a_s0`: the line `s = d + e` in `d`, `p = 3d + 2e`, `q = 2d + e`;
    - cone A with `d < a_d0` (`d >= 1`): the line `p = 2q - d`;
    - cone B with `s < b_s0` (`s >= 1`): the line `p = q + s`;
    - cone B with `e < b_d0` (`e >= 1`): the line `d = s + e` in `s`, `p = 3s + e`, `q = 2s + e`."""
    var out = List[List[Int]]()
    for e in range(a_s0):
        out.append([2 * e, 3, 0, e, 2, 0, branch])
    for d in range(1, a_d0):
        out.append(slope_family(2, -d, branch))
    for s in range(1, b_s0):
        out.append(slope_family(1, s, branch))
    for e in range(1, b_d0):
        out.append([e, 3, 0, e, 2, 0, branch])
    return out^


# Pinned cone verdicts: branch, which, s0, d0, symbolic vertices.
def wedge_pins() -> List[List[Int]]:
    return [
        [1, 0, 9, 9, 74],
        [1, 1, 9, 1, 74],
        [-1, 0, 9, 9, 171],
        [-1, 1, 9, 5, 123],
    ]


def cone_pin(branch: Int, which: Int) raises -> List[Int]:
    var pins = wedge_pins()
    for i in range(len(pins)):
        if pins[i][0] == branch and pins[i][1] == which:
            return pins[i].copy()
    raise Error("no pinned verdict for this cone")


def check_cone_pin(v: ConeVerdict, pin: List[Int]) raises:
    if v.s0 != pin[2] or v.d0 != pin[3] or v.symbolic_vertices != pin[4]:
        raise Error("the cone's verdict differs from its pin in wedge_pins()")


def pinned_boundary(branch: Int) raises -> List[List[Int]]:
    """`wedge_boundary` at the pinned cone thresholds."""
    var a = cone_pin(branch, 0)
    var b = cone_pin(branch, 1)
    return wedge_boundary(branch, a[2], a[3], b[2], b[3])


# Pinned boundary-line verdicts: the family (7 entries), then q0, symbolic
# vertices, PIP members below q0, non-PIP members below q0, parameters below q0
# outside class B.
def boundary_pins() -> List[List[Int]]:
    return List[List[Int]]()


def boundary_pin(f: List[Int]) raises -> List[Int]:
    var pins = boundary_pins()
    for i in range(len(pins)):
        var same = True
        for k in range(7):
            if pins[i][k] != f[k]:
                same = False
        if same:
            return pins[i].copy()
    raise Error("no pinned verdict for this boundary line")


def check_line_pin(v: LineVerdict, pin: List[Int]) raises:
    if (
        v.q0 != pin[7]
        or v.symbolic_vertices != pin[8]
        or v.finite_members != pin[9]
        or v.finite_non_pip != pin[10]
        or v.finite_outside != pin[11]
    ):
        raise Error("the boundary line's verdict differs from its pin in boundary_pins()")


def family_string(f: List[Int]) -> String:
    var out = String("[")
    for k in range(len(f)):
        out += String(f[k]) + ("" if k == len(f) - 1 else ", ")
    return out + "]"


def report_cone(branch: Int, which: Int) raises:
    var v = certify_cone(branch, which)
    print("class B wedge, branch", branch, "cone", "A" if which == 0 else "B", "family", family_string(cone_family(branch, which)), ":")
    print("  symbolic graph on the quadrant (", v.s0, ",", v.d0, ") and up:", v.symbolic_vertices, "vertices, all hitting;", v.queries, "certified sign reads")
    print("  cross-check at four quadrant points: symbolic graph = exact graph")
    check_cone_pin(v, cone_pin(branch, which))
    print("  pinned verdict reproduced")


def report_boundary(branch: Int, part: Int, parts: Int) raises:
    var lines = pinned_boundary(branch)
    for i in range(len(lines)):
        if i % parts != part:
            continue
        var v = certify_family_line(lines[i])
        print("boundary line", family_string(lines[i]), ": q0", v.q0, "vertices", v.symbolic_vertices, "finite", v.finite_members, v.finite_non_pip, v.finite_outside)
        check_line_pin(v, boundary_pin(lines[i]))
    print("  boundary part", part, "of", parts, "for branch", branch, ": pinned verdicts reproduced")


def mode_of(args: List[String]) raises -> String:
    """`cone BRANCH WHICH`, `boundary BRANCH PART PARTS` or `wedge BRANCH`; any
    other shape raises."""
    for i in range(1, len(args)):
        _ = Int(args[i])  # raises unless an integer
    if len(args) == 3 and args[0] == "cone":
        return "cone"
    if len(args) == 4 and args[0] == "boundary" and Int(args[3]) >= 1 and 0 <= Int(args[2]) < Int(args[3]):
        return "boundary"
    if len(args) == 2 and args[0] == "wedge":
        return "wedge"
    raise Error("usage: symbolic_wedge_certificate.mojo cone BRANCH WHICH | boundary BRANCH PART PARTS | wedge BRANCH")


def main() raises:
    var argv_ = argv()
    var args = List[String]()
    for i in range(1, len(argv_)):
        args.append(String(argv_[i]))
    var mode = mode_of(args)
    var branch = Int(args[1])
    if mode == "cone":
        report_cone(branch, Int(args[2]))
    elif mode == "boundary":
        report_boundary(branch, Int(args[2]), Int(args[3]))
    else:
        report_cone(branch, 0)
        report_cone(branch, 1)
        report_boundary(branch, 0, 1)
        print("class B wedge q < p < 2q, branch", branch, ": certified")
