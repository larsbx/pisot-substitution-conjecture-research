"""Complete candidate cover for the plus positive-b class-D quadrant.

The changing-realness obstruction of sealed row 12 is isolated to the integer
interface c=5a+6 (c=b-1).  The whole quadrant is decomposed exactly into five
low unimodular wedges, six affine lines c=5a+j (j=1..6), and one high
unimodular wedge.  Each wedge core and every boundary strip it leaves are
certified by the existing exact ClassWedge/ClassLine engines.
"""
from std.sys import argv
from symbolic_line_certificate import ClassLine, ClassWedge, certify, certify_wedge, wedge_edges
from a1_normal_form_census import CLASS_D


def _low_wedge(k: Int) raises -> ClassWedge:
    if k < 0 or k > 4:
        raise Error("low chamber index must be 0..4")
    return ClassWedge(CLASS_D, [
        4, 3+k, 4+k,
        3, 3+k, 4+k,
        1, 2+k, 3+k,
    ])


def _high_wedge() raises -> ClassWedge:
    # (a,c)=(0,7)+u(1,5)+v(0,1).
    return ClassWedge(CLASS_D, [11,8,1, 10,8,1, 8,7,1])


def _interface_line(j: Int) raises -> ClassLine:
    if j < 1 or j > 6:
        raise Error("plus chamber line index must be 1..6")
    # c=5a+j: p=8a+4+j, q=8a+3+j, r=7a+1+j.
    return ClassLine(CLASS_D, [8,4+j, 8,3+j, 7,1+j], True)


def _complete_wedge(spec: ClassWedge) raises -> List[Int]:
    print("BEGIN_WEDGE_CORE", spec.describe())
    var core = certify_wedge(spec)
    print("WEDGE_CORE_CERTIFIED", "u0=", core.a0, "v0=", core.b0, "vertices=", core.symbolic_vertices)
    var edges = wedge_edges(spec,core.a0,core.b0)
    var finite = 0
    for i in range(len(edges)):
        print("BEGIN_BOUNDARY_LINE", i, edges[i].describe())
        var v = certify(edges[i])
        print("BOUNDARY_LINE_CERTIFIED", i, "q0=", v.q0, "finite_pip=", v.finite_members)
        finite += v.finite_members
    return [core.a0,core.b0,core.symbolic_vertices,len(edges),finite]


def classify_plus_chamber(a: Int, c: Int) raises -> List[Int]:
    """Exact lattice partition witness for a>=0,c>=0.

    Returns [kind,index,u,v]: kind 0=low wedge, 1=line, 2=high wedge.
    """
    if a < 0 or c < 0:
        raise Error("plus chamber parameters must be nonnegative")
    if c <= 5*a:
        if a == 0:
            return [0,0,0,0]
        var k = c // a
        if k > 4:
            k = 4
        var u = (k+1)*a-c
        var v = c-k*a
        if u < 0 or v < 0 or u+v != a or k*u+(k+1)*v != c:
            raise Error("low wedge inverse failed")
        return [0,k,u,v]
    var j = c-5*a
    if j <= 6:
        return [1,j,a,0]
    var v = c-5*a-7
    if v < 0:
        raise Error("high wedge inverse failed")
    return [2,0,a,v]


def certify_plus_positive_b_chambers() raises -> List[Int]:
    var wedges = 0
    var explicit_lines = 0
    var boundary_lines = 0
    var finite_prefix = 0
    var max_vertices = 0

    for k in range(5):
        print("BEGIN_LOW_WEDGE", k)
        var w = _complete_wedge(_low_wedge(k))
        wedges += 1
        boundary_lines += w[3]
        finite_prefix += w[4]
        max_vertices = max(max_vertices,w[2])

    var h = _complete_wedge(_high_wedge())
    wedges += 1
    boundary_lines += h[3]
    finite_prefix += h[4]
    max_vertices = max(max_vertices,h[2])

    for j in range(1,7):
        print("BEGIN_INTERFACE_LINE", j)
        var v = certify(_interface_line(j))
        explicit_lines += 1
        finite_prefix += v.finite_members
        max_vertices = max(max_vertices,v.symbolic_vertices)

    if wedges != 6 or explicit_lines != 6:
        raise Error("plus chamber cover count changed")
    return [wedges,explicit_lines,boundary_lines,finite_prefix,max_vertices]


def main() raises:
    # Component runs expose later refusals even if the aggregate stops early.
    # They never emit the whole-quadrant receipt.
    var args = argv()
    if len(args) > 1:
        var kind = String(args[1])
        if kind == "low" and len(args) == 3:
            var k = Int(String(args[2]))
            print("BEGIN_LOW_WEDGE", k)
            var w = _complete_wedge(_low_wedge(k))
            print("PLUS_CHAMBER_COMPONENT_CERTIFIED", "low", k, "boundary_lines=", w[3])
            return
        if kind == "high" and len(args) == 2:
            var w = _complete_wedge(_high_wedge())
            print("PLUS_CHAMBER_COMPONENT_CERTIFIED", "high", "boundary_lines=", w[3])
            return
        if kind == "line" and len(args) == 3:
            var j = Int(String(args[2]))
            print("BEGIN_INTERFACE_LINE", j)
            var v = certify(_interface_line(j))
            print("PLUS_CHAMBER_COMPONENT_CERTIFIED", "line", j, "q0=", v.q0, "vertices=", v.symbolic_vertices, "finite_pip=", v.finite_members)
            return
        raise Error("usage: class_d_plus_positive_b_chambers.mojo [low 0..4 | high | line 1..6]")
    var out = certify_plus_positive_b_chambers()
    print(
        "CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED",
        "wedges=", out[0],
        "explicit_lines=", out[1],
        "boundary_lines=", out[2],
        "finite_prefix_pip=", out[3],
        "max_symbolic_vertices=", out[4],
    )
