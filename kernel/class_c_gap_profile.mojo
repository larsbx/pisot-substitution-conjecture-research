"""Class-C gaps: exact finite profile of `(n+d, n, n-d+eps)`; no uniform claim.

  mojo run -I . class_c_gap_profile.mojo profile D EPS NMIN NMAX
      one block per member n (or `S n reason` for a screened non-PIP member)
  mojo run -I . class_c_gap_profile.mojo same EPS DMIN DMAX DSTEP OFF_LO OFF_HI
      for gaps DMIN, DMIN+DSTEP, .. <= DMAX and every n = 4d + off with
      OFF_LO <= off <= OFF_HI: refuses an empty scan, a screened member, or any
      member whose label set differs from the first; prints that common set. The
      frozen tail is `same 1 5 30 1 0 24` and `same -1 5 30 1 4 28` (onsets 4d, 4d+4).
  mojo run -I . class_c_gap_profile.mojo diagonals EPS DMIN DMAX JMAX
      vertex counts at n = 4d - j, j = -4..JMAX, one row per j
"""
from std.sys import argv
from psc.class_c_gap_profile import c_block, same_label_set, scan_range, vertices_of


def main() raises:
    var a = argv()
    if len(a) == 6 and a[1] == "profile":
        scan_range(Int(a[4]), Int(a[5]), "n")
        for n in range(Int(a[4]), Int(a[5]) + 1):
            if n - Int(a[2]) + Int(a[3]) >= 0:
                print(c_block(Int(a[2]), Int(a[3]), n), end="")
        return
    if len(a) == 8 and a[1] == "same":
        var r = same_label_set(Int(a[2]), Int(a[3]), Int(a[4]), Int(a[5]), Int(a[6]), Int(a[7]))
        print("SAME_LABEL_SET eps=" + a[2], "gaps", a[3] + ".." + a[4] + " step " + a[5],
              "n=4d+" + a[6] + ".." + a[7], "members", r[0], "rows", len(r[1].splitlines()),
              "; finite observation, no uniform claim")
        print(r[1], end="")
        return
    if len(a) == 6 and a[1] == "diagonals":
        var eps = Int(a[2])
        scan_range(Int(a[3]), Int(a[4]), "gap")
        scan_range(-4, Int(a[5]), "diagonal")
        for j in range(-4, Int(a[5]) + 1):
            var line = "j=" + String(j)
            for d in range(Int(a[3]), Int(a[4]) + 1):
                var n = 4 * d - j
                if n - d + eps < 0:
                    line += " ."
                    continue
                var block = c_block(d, eps, n)
                line += " " + ("." if block.startswith("S ") else String(vertices_of(block)))
            print(line)
        return
    raise Error("usage: profile D EPS NMIN NMAX | same EPS DMIN DMAX DSTEP OFF_LO OFF_HI | diagonals EPS DMIN DMAX JMAX")
