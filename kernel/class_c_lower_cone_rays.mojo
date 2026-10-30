"""Conditional BH certificate attempts for the first lower-cone fixed-k rays.

Fix k=n-3d in {-1,-2}. Use STRIP coordinate j=4d-n=d-k, so
d=k+j, n=4k+3j. For d>=D the existing symbolic cone engine treats
j>=D-k as a one-parameter orthant; *no frozen-label hypothesis* is used.

  mojo run -I . class_c_lower_cone_rays.mojo 1 1
  mojo run -I . class_c_lower_cone_rays.mojo -1 2

EPS must be +-1; T=1 or 2 represents k=-T. A successful receipt proves
only boundary hitting of the canonical swap-seed overlap graph, subject to
Lemma S' and the trusted symbolic_cone implementation. Refusals are not
counterexamples, and a capped finite graph never counts as a witness.
"""
from std.sys import argv
from psc.class_c_gap_profile import c_block, c_member, vertices_of
from psc.class_c_tail_certificate import GAP, STRIP, Piece, tail_cone, vertex_keys
from psc.symbolic_cone import ConeGraph, symbolic_cone_graph, cone_offset_zero_reachable
from symbolic_line_certificate import exact_vertex_keys, same_set


def inconclusive(msg: String) -> Bool:
    return msg.startswith("a sign") or msg.startswith("a fitted") or msg.startswith("a run-position")


def certify_ray(eps: Int, t: Int) raises:
    if eps != 1 and eps != -1:
        raise Error("EPS must be +1 or -1")
    if t < 1 or t > 2:
        raise Error("only k=n-3d=-1,-2 are scoped")
    var k = -t
    for D in range(7, 25):
        # The fixed-k line is GAP in the (k,j) STRIP frame; j=d-k grows.
        # PIP for all d>=7 is already a hand-proved consequence of P_C,
        # but the symbolic code must independently certify it as a guard.
        var piece = Piece(eps, 0, k, D - k, GAP, STRIP)
        var g: ConeGraph
        try:
            g = symbolic_cone_graph(tail_cone(piece), piece.region())
        except e:
            if not inconclusive(String(e)):
                raise e^
            print("UNDECIDED eps=", eps, "k=", k, "D=", D)
            continue
        if not g.pip:
            raise Error("symbolic PIP guard refused on a PIP ray: " + g.reason)
        for good in cone_offset_zero_reachable(g):
            if not good:
                raise Error("symbolic vertex lacks an offset-zero descendant")
        # Both cross-checks are complete vertex-key sets; the proof of
        # universality is the symbolically certified closure, not sampling.
        for d in [D + 1, D + 2]:
            var j = d - k
            if not same_set(vertex_keys(g, 0, j), exact_vertex_keys(c_member(d, eps, 3 * d + k))):
                raise Error("exact member and symbolic vertex keys disagree")
        var count = 0
        for d in range(7, D):
            var n = 3 * d + k
            var block = c_block(d, eps, n)
            if block.startswith("S "):
                raise Error("exact PIP member was screened out")
            print("FINITE eps=", eps, "k=", k, "d=", d, "n=", n, "vertices=", vertices_of(block))
            count += 1
        print("BH_CERTIFIED eps=", eps, "k=", k, "d>=7",
              "symbolic onset D=", D, "vertices=", g.size(),
              "finite exceptions=", count, "sign queries=", g.queries,
              "Polya exponent=", g.polya)
        return
    raise Error("NO_CERTIFICATE: shifted ray closure not decided through D=24; BH remains open")


def main() raises:
    var a = argv()
    if len(a) != 3:
        raise Error("usage: class_c_lower_cone_rays.mojo EPS T (T=1 or 2)")
    certify_ray(Int(a[1]), Int(a[2]))
