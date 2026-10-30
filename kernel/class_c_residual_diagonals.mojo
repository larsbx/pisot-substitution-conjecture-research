"""Attempt the first residual class-C BH diagonals uniformly in d >= 6.

Uses the existing (trusted) symbolic cone closure for d >= 8, and the
independent finite exact overlap kernel for d = 6,7. Raises unless every
vertex hits offset zero AND all three pieces have exactly the same labels.
This is a scoped BH certificate, not a pure discrete spectrum proof.

  mojo run -I . class_c_residual_diagonals.mojo 1
  mojo run -I . class_c_residual_diagonals.mojo -1
"""
from std.sys import argv
from psc.class_c_gap_profile import c_block, rows_of, vertices_of
from psc.class_c_tail_certificate import DIAGONAL, Piece, certify_piece, rows


def main() raises:
    var a = argv()
    if len(a) != 2:
        raise Error("usage: class_c_residual_diagonals.mojo EPS (+1 or -1)")
    var eps = Int(a[1])
    if eps != 1 and eps != -1:
        raise Error("eps must be +-1")
    var c = -1 if eps == 1 else 3
    var g = certify_piece(Piece(eps, c, 8, 0, DIAGONAL))
    var size = 198 if eps == 1 else 216
    if g.size() != size:
        raise Error("first lower diagonal has an unexpected vertex count")
    var common = rows(g)
    for d in [6, 7]:
        var n = 4 * d + c
        var block = c_block(d, eps, n)
        if block.startswith("S "):
            raise Error("a residual diagonal member is screened out")
        if vertices_of(block) != size or rows_of(block) != common:
            raise Error("the d=6/7 residual diagonal does not agree with the symbolic tail")
        print("eps=", eps, "d=", d, "n=", n, "exact", size, "vertices")
    print("BH_CERTIFIED eps=", eps, "d>=6 n=4d+", c, "vertices", g.size(),
          "typed rows", len(common.splitlines()))
    print(common, end="")
