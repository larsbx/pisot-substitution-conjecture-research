"""Class-C residual-diagonal boundary-hitting cover, without a frozen-label axiom.

For EPS=+-1 and 2 <= J <= 5, this driver tries to certify *all* positive-gap
members n=4d+(0 if EPS=1 else 4)-J, d>=6. It can only succeed after:

  * a full parameter-uniform symbolic swap-seed closure for d>=D,
  * certified PIP and an identically-zero descendant of every vertex,
  * exact vertex-set cross-checks at D+1 and D+2,
  * exhaustive uncapped exact member checking for every integer 6<=d<D.

Undecided symbolic signs / affine fits cause a larger D to be tried.
A non-hitting symbolic vertex, exact mismatch, screening refusal or cap
is a hard failure, never an "inconclusive" success.

Crucially, no label-set equality is required between different parameters
or pieces. The property proved is BH only, *not* frozen labels, G1 or PDS.
Proof conditional on Lemma S' and trusted cone implementation.

  mojo run -I . class_c_residual_diagonal_cover.mojo 1 2
  mojo run -I . class_c_residual_diagonal_cover.mojo -1 5
"""
from std.sys import argv
from psc.class_c_gap_profile import c_block, c_member, vertices_of
from psc.class_c_tail_certificate import DIAGONAL, Piece, tail_cone, vertex_keys
from psc.symbolic_cone import ConeGraph, cone_offset_zero_reachable, symbolic_cone_graph
from symbolic_line_certificate import exact_vertex_keys, same_set


def low_gap(j: Int, eps: Int) raises -> Int:
    """Proved class-C PIP threshold n>=2d-3eps-2, for n=4d+c-j."""
    if eps != 1 and eps != -1:
        raise Error("EPS must be +1 or -1")
    if j < 2 or j > 5:
        raise Error("only residual diagonals j=2..5 are in this scoped cover")
    var c = 0 if eps == 1 else 4
    var d = 6
    while 4 * d + c - j < 2 * d - 3 * eps - 2:
        d += 1
    return d


def recoverable(msg: String) -> Bool:
    """Only sound but incomplete decision readers may prompt a shift."""
    return msg.startswith("a sign") or msg.startswith("a fitted") or msg.startswith("a run-position")


def certify(eps: Int, j: Int) raises:
    var first = low_gap(j, eps)
    var c = (0 if eps == 1 else 4) - j
    # More shifts are allowed than in T_C, but no unspecified infinite search.
    for d0 in range(first, 17):
        var p = Piece(eps, c, d0, 0, DIAGONAL)
        var g: ConeGraph
        try:
            g = symbolic_cone_graph(tail_cone(p), p.region())
        except e:
            if not recoverable(String(e)):
                raise e^
            print("INCONCLUSIVE eps=", eps, "j=", j, "d>=", d0,
                  "symbolic signs or fit undecided")
            continue
        if not g.pip:
            raise Error("PIP certificate refused on a mathematically PIP diagonal: " + g.reason)
        var good = cone_offset_zero_reachable(g)
        for x in good:
            if not x:
                raise Error("symbolic vertex lacks an offset-zero descendant (not a BH certificate)")
        # Exact-graph cross-checks: two distinct interior points, not proof by
        # sampling; Lemma S' supplies the quantified implication.
        for d in [d0 + 1, d0 + 2]:
            if not same_set(vertex_keys(g, d, 0), exact_vertex_keys(c_member(d, eps, 4 * d + c))):
                raise Error("exact cross-check differs from symbolic closure")
        # Every omitted member is decided by the exact, capped, fail-closed
        # graph kernel; c_block refuses a non-PIP, cap or nonhitting graph.
        var exact = 0
        for d in range(first, d0):
            var n = 4 * d + c
            var block = c_block(d, eps, n)
            if block.startswith("S "):
                raise Error("PIP lower-domain member screened by finite kernel")
            print("EXACT eps=", eps, "j=", j, "d=", d, "n=", n,
                  "vertices", vertices_of(block))
            exact += 1
        print("BH_CERTIFIED eps=", eps, "j=", j, "d>=", first,
              "n=4d+", c, "symbolic onset d=", d0,
              "symbolic vertices", g.size(), "finite exceptions", exact,
              "sign queries", g.queries, "Polya exponent", g.polya)
        return
    raise Error("NO_CERTIFICATE: finite shifted diagonal search exhausted; BH status inconclusive")


def main() raises:
    var a = argv()
    if len(a) != 3:
        raise Error("usage: class_c_residual_diagonal_cover.mojo EPS J")
    certify(Int(a[1]), Int(a[2]))
