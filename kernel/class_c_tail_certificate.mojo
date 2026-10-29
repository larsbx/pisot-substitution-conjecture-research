"""Theorems T_C and T_C2 on class C (docs/class-c-tail-theorem-2026-10-28.md, docs/class-c-strip-stopgo-2026-10-29.md).

  mojo run -I . class_c_tail_certificate.mojo theorem EPS
      covers every member d >= 6, n >= 4d (EPS = 1) or n >= 4d + 4 (EPS = -1):
      one line per piece or exact member, then the common label set as typed rows
  mojo run -I . class_c_tail_certificate.mojo strip EPS
      covers every member 3d <= n below the onset (n < 4d plus, n < 4d + 4
      minus), every gap, in the frame (k, j) = (n - 3d, 4d - n): one line per
      piece or exact member, then the distinct label sets
  mojo run -I . class_c_tail_certificate.mojo piece EPS C D0 M0 cone|diagonal|gap [strip]
      one piece alone (`psc.class_c_tail_certificate.Piece`), then its label set;
      with `strip`, D0 and M0 are k0 and j0 and C must be 0

Every mode raises unless everything it names is certified: PIP on every piece,
every vertex hitting offset zero, constant offsets, the exact cross-check, and
(theorem only) one label set across all pieces and members.
"""
from std.sys import argv
from psc.class_c_gap_profile import frozen_onset
from psc.class_c_tail_certificate import CONE, DIAGONAL, GAP, STRIP, TAIL, Cover, Piece, certify_piece, cover, rows

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
    if len(a) == 3 and a[1] == "strip":
        var eps = Int(a[2])
        var out = Cover(True, False)
        cover(Piece(eps, 0, 0, 1, CONE, STRIP), out)
        if eps == -1:
            for j in range(-3, 1):  # n = 4d - j in 4d..4d+3, k = n - 3d >= 1 - j so that d >= 1
                cover(Piece(eps, 0, 1 - j, j, DIAGONAL, STRIP), out)
        print("T_C2 eps=" + String(eps), "3d<=n<" + ("4d" if eps == 1 else "4d+4"),
              "symbolic pieces", len(out.pieces), "exact members", out.members, "distinct label sets", len(out.sets))
        for i in range(len(out.sets)):
            print("SET", i, "typed rows", len(out.sets[i].splitlines()))
            print(out.sets[i], end="")
        return
    if (len(a) == 7 or (len(a) == 8 and a[7] == "strip")) and a[1] == "piece":
        var p = Piece(Int(a[2]), Int(a[3]), Int(a[4]), Int(a[5]), kind_of(a[6]), STRIP if len(a) == 8 else TAIL)
        var g = certify_piece(p)
        print(p.name(), "vertices", g.size())
        print(rows(g), end="")
        return
    raise Error("usage: theorem EPS | strip EPS | piece EPS C D0 M0 cone|diagonal|gap [strip]")
