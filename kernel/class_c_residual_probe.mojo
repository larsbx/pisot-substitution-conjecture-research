"""BH-only parametric class-C probe: no frozen-label-set precondition.

Inputs are a shifted cone, diagonal or gap line with n=4d+c+m.
Returns a quantified BH certificate ONLY when the underlying symbolic
closure fully decides all signs, every symbolic vertex reaches offset zero,
and one independently built exact graph matches its instantiated vertices.

This is not a substitute for independent verification of symbolic_cone.mojo.
A sign or fitting refusal is INCONCLUSIVE, not a counterexample.

  mojo run -I . class_c_residual_probe.mojo 1 -2 8 0 diagonal
  mojo run -I . class_c_residual_probe.mojo -1 2 8 0 diagonal
  mojo run -I . class_c_residual_probe.mojo 1 -10 12 0 gap
"""
from std.sys import argv
from psc.class_c_gap_profile import c_member
from psc.class_c_tail_certificate import CONE, DIAGONAL, GAP, Piece, tail_cone, vertex_keys
from psc.symbolic_cone import symbolic_cone_graph, cone_offset_zero_reachable
from symbolic_line_certificate import exact_vertex_keys, same_set


def kind_of(x: String) raises -> Int:
    if x == "cone":
        return CONE
    if x == "diagonal":
        return DIAGONAL
    if x == "gap":
        return GAP
    raise Error("kind must be cone, diagonal or gap")


def main() raises:
    var a = argv()
    if len(a) != 6:
        raise Error("usage: EPS C D0 M0 cone|diagonal|gap")
    var p = Piece(Int(a[1]), Int(a[2]), Int(a[3]), Int(a[4]), kind_of(a[5]))
    var g = symbolic_cone_graph(tail_cone(p), p.region())
    if not g.pip:
        raise Error("piece not certified PIP: " + g.reason)
    var hit = cone_offset_zero_reachable(g)
    for x in hit:
        if not x:
            raise Error("symbolic vertex has no offset-zero descendant")
    var s1 = 0 if p.kind == GAP else p.d0 + 1
    var s2 = 0 if p.kind == DIAGONAL else p.m0 + 2
    var dn = p.member(s1, s2)
    if not same_set(vertex_keys(g, s1, s2), exact_vertex_keys(c_member(dn[0], p.eps, dn[1]))):
        raise Error("exact oracle and symbolic vertex labels disagree")
    # This deliberately omits class_c_tail_certificate.labels(g):
    # parameter-dependent offsets do not invalidate BH.
    print("BH_CERTIFIED", p.name(), "vertices", g.size(),
          "sign queries", g.queries, "Polya", g.polya)
