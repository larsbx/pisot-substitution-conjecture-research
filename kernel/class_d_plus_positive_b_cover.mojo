"""Exact positive-b closure/hitting certificate for the sealed 718-row plus carrier.

The b=0 carrier is proposed only as an upper cover. On an eventual two-parameter
core, exact Perron-sign decisions determine which labels remain real, every
real label is expanded once, nonterminal escapes are forbidden, and zero
reachability is checked on the resulting closed graph. Boundary strips outside
that core are certified by the existing exact line engine.
"""
from std.collections import Dict
from psc.param_poly import QX, qx_const
from psc.symbolic_line import (
    Eventual, SymVertex, SymbolicLineGraph, _Closure,
    certify_wedge_pisot, zero_descendants,
)
from psc.class_d_plus_cover_data import plus_cover_rows
from symbolic_line_certificate import ClassWedge, wedge_edges, certify
from a1_normal_form_census import CLASS_D


struct PlusCoverVerdict(Copyable, Movable):
    var a0: Int
    var b0: Int
    var real_cover_vertices: Int
    var extra_coincidences: Int
    var boundary_lines: Int

    def __init__(out self):
        self.a0 = -1
        self.b0 = -1
        self.real_cover_vertices = 0
        self.extra_coincidences = 0
        self.boundary_lines = 0


def _const_vertex(row: List[Int]) -> SymVertex:
    var w = List[QX]()
    w.append(qx_const(row[2]))
    w.append(qx_const(row[3]))
    w.append(qx_const(row[4]))
    return SymVertex(row[0], row[1], w^)


def certify_plus_positive_b_cover() raises -> PlusCoverVerdict:
    # c=b-1>=0: (p,q,r)=(4,3,1)+a(3,3,2)+c(1,1,1)
    var spec = ClassWedge(CLASS_D, [4,3,1, 3,3,1, 1,2,1])
    var line = spec.line()
    var ev = Eventual()
    var pip = certify_wedge_pisot(line, ev)
    if not pip.holds:
        raise Error("plus positive-b family did not certify PIP")

    var cl = _Closure(line^, pip.ell_sign, ev^)
    var rows = plus_cover_rows()
    var cover = Dict[String, Int]()
    for i in range(len(rows)):
        var v = _const_vertex(rows[i])
        var k = v.key()
        if k in cover:
            raise Error("duplicate sealed plus-cover label")
        cover[k] = i

    # Only labels uniformly real on the certified core are active states.
    var active = List[Int]()
    for i in range(len(rows)):
        var v = _const_vertex(rows[i])
        if cl.real(v.top, v.bottom, v.w):
            active.append(cl.intern(v^))

    # Every real seed must lie in the sealed upper cover or be a coincidence.
    cl.seeds()
    for i in range(len(cl.vertices)):
        var v = cl.vertices[i]
        if v.key() not in cover and not (v.top == v.bottom and v.is_zero_offset()):
            raise Error("plus positive-b seed escapes sealed cover")

    # Expand each active cover label exactly once.
    for i in active:
        cl.expand(i)

    var extras = 0
    for i in range(len(cl.vertices)):
        var v = cl.vertices[i]
        if v.key() in cover:
            continue
        if v.top == v.bottom and v.is_zero_offset():
            extras += 1
            continue
        raise Error("plus positive-b child escapes sealed 718-label cover")

    # Closed-cover BH: every active state must reach an offset-zero state.
    var zero = List[Bool]()
    for i in range(len(cl.vertices)):
        zero.append(cl.vertices[i].is_zero_offset())
    var good = zero_descendants(cl.adj, zero)
    for i in active:
        if not good[i]:
            raise Error("plus positive-b sealed-cover vertex has no offset-zero descendant")

    var out = PlusCoverVerdict()
    out.real_cover_vertices = len(active)
    out.extra_coincidences = extras
    out.a0 = cl.ev.first_integer_above()
    out.b0 = cl.ev.b_floor

    var edges = wedge_edges(spec, out.a0, out.b0)
    out.boundary_lines = len(edges)
    for i in range(len(edges)):
        _ = certify(edges[i])
    return out^


def main() raises:
    var v = certify_plus_positive_b_cover()
    print(
        "COMPLETE_PLUS_POSITIVE_B_COVER",
        "a0=", v.a0,
        "b0=", v.b0,
        "real_cover_vertices=", v.real_cover_vertices,
        "extra_coincidences=", v.extra_coincidences,
        "boundary_lines=", v.boundary_lines,
    )
