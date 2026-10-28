"""Theorem T_C: the class-C frozen tail for every gap d >= 6 (docs/class-c-tail-theorem-2026-10-28.md).

  mojo run -I . class_c_tail_certificate.mojo theorem EPS
      covers every member d >= 6, n >= 4d (EPS = 1) or n >= 4d + 4 (EPS = -1):
      one line per piece or exact member, then the common label set as typed rows
  mojo run -I . class_c_tail_certificate.mojo piece EPS C D0 M0 cone|diagonal|gap
      one piece alone (`psc.class_c_tail_certificate.Piece`), then its label set

Either mode raises unless everything it names is certified: PIP on every piece,
every vertex hitting offset zero, constant offsets, the exact cross-check, and
one label set across all pieces and members.
"""
from std.sys import argv
from psc.class_c_gap_profile import frozen_onset
from psc.class_c_tail_certificate import CONE, DIAGONAL, GAP, Cover, Piece, certify_piece, cover, rows

comptime GAP_FLOOR = 6


def kind_of(name: String) raises -> Int:
    if name == "cone":
        return CONE
    if name == "diagonal":
        return DIAGONAL
    if name == "gap":
        return GAP
    raise Error("piece kind must be cone, diagonal or gap")


def main() raises:
    var a = argv()
    if len(a) == 3 and a[1] == "theorem":
        var eps = Int(a[2])
        var out = Cover(True)
        cover(Piece(eps, frozen_onset(0, eps), GAP_FLOOR, 0, CONE), out)
        print("T_C eps=" + String(eps), "d>=" + String(GAP_FLOOR), "n-4d>=" + String(frozen_onset(0, eps)),
              "symbolic pieces", len(out.pieces), "exact members", out.members,
              "typed rows", len(out.rows.splitlines()))
        print(out.rows, end="")
        return
    if len(a) == 7 and a[1] == "piece":
        var p = Piece(Int(a[2]), Int(a[3]), Int(a[4]), Int(a[5]), kind_of(a[6]))
        var g = certify_piece(p)
        print(p.name(), "vertices", g.size())
        print(rows(g), end="")
        return
    raise Error("usage: theorem EPS | piece EPS C D0 M0 cone|diagonal|gap")
