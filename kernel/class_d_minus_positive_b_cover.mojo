"""Exact positive-b closure certificate for the sealed 145-row minus spine.

This proves only the cover-closure half of the transported rank argument on an
eventual two-parameter core. Boundary lines outside the certified core are
returned for the existing exact line engine. No graph discovery or sampled
plateau is used.
"""
from std.collections import Dict
from psc.param_poly import QX, qx_const
from psc.symbolic_line import Eventual, SymVertex, _Closure, certify_wedge_pisot
from psc.class_d_minus_spine_data import minus_spine_rows
from symbolic_line_certificate import ClassWedge, wedge_edges, certify
from a1_normal_form_census import CLASS_D


struct CoverVerdict(Copyable, Movable):
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


def certify_minus_positive_b_cover() raises -> CoverVerdict:
    # c=b-1>=0: (p,q,r)=(6,7,5)+a(3,3,2)+c(1,1,1)
    var spec = ClassWedge(CLASS_D, [6,3,1, 7,3,1, 5,2,1])
    var line = spec.line()
    var ev = Eventual()
    var pip = certify_wedge_pisot(line, ev)
    if not pip.holds:
        raise Error("minus positive-b family did not certify PIP")

    var cl = _Closure(line^, pip.ell_sign, ev^)
    var rows = minus_spine_rows()
    var cover = Dict[String, Int]()

    # Register the sealed labels as the only allowed nonterminal carrier.
    for i in range(len(rows)):
        var v = _const_vertex(rows[i])
        var k = v.key()
        if k in cover:
            raise Error("duplicate sealed cover label")
        cover[k] = i

    # Every uniformly-real sealed label must be closed under all actual children.
    var real_ids = List[Int]()
    for i in range(len(rows)):
        var v = _const_vertex(rows[i])
        if cl.real(v.top, v.bottom, v.w):
            real_ids.append(cl.intern(v^))

    # Every uniformly-real seed must already be in the sealed carrier, unless it
    # is an actual coincidence (which is terminal and harmless for BH).
    cl.seeds()
    for i in range(len(cl.vertices)):
        var v = cl.vertices[i]
        if v.key() not in cover and not (v.top == v.bottom and v.is_zero_offset()):
            raise Error("positive-b seed escapes sealed cover")

    var before = len(cl.vertices)
    for i in real_ids:
        cl.expand(i)

    var extras = 0
    for i in range(len(cl.vertices)):
        var v = cl.vertices[i]
        if v.key() in cover:
            continue
        if v.top == v.bottom and v.is_zero_offset():
            extras += 1
            continue
        raise Error("positive-b child escapes sealed 145-label cover")

    var out = CoverVerdict()
    out.real_cover_vertices = len(real_ids)
    out.extra_coincidences = extras
    out.a0 = cl.ev.first_integer_above()
    out.b0 = cl.ev.b_floor

    # The complement of the certified core is a finite family of exact lines.
    var edges = wedge_edges(spec, out.a0, out.b0)
    out.boundary_lines = len(edges)
    for i in range(len(edges)):
        var verdict = certify(edges[i])
        # certify(line) raises on any PIP member that fails BH.
        _ = verdict
    return out^


def main() raises:
    var v = certify_minus_positive_b_cover()
    print(
        "COMPLETE_MINUS_POSITIVE_B_COVER",
        "a0=", v.a0,
        "b0=", v.b0,
        "real_cover_vertices=", v.real_cover_vertices,
        "extra_coincidences=", v.extra_coincidences,
        "boundary_lines=", v.boundary_lines,
    )
