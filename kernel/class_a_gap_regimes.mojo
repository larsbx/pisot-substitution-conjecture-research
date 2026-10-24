"""Class-A gaps d>=5: resumable exact label datasets and their regime fits.

  mojo run -I . class_a_gap_regimes.mojo build D EPS LMIN LMAX DIR [WORKERS] [BATCH]
      members n = d l + r, LMIN <= l <= LMAX, of (n+d,n,n+eps); appends to
      DIR/labels-dD-epsE.txt, skipping members already recorded
  mojo run -I . class_a_gap_regimes.mojo fit EPS DIR DMIN DMAX J LMIN OUT [MOJO_OUT]
      for regimes low r=0..J-1, high r=d-1..d-J and middle J<=r<=d-J-1, the
      least gap d0 >= DMIN from which one fit holds for all d0<=d<=DMAX;
      fitted tables go to OUT; with MOJO_OUT, the rows are also written as a
      Mojo data module in ray-row format (refusing any n, d or r coefficient)
"""
from std.sys import argv
from std.collections import Dict
from psc.class_a_gap_dataset import extend_dataset, members
from psc.class_a_gap_regimes import LOW, HIGH, MIDDLE, RegimeFit, fit_regime, regime_name


def regime_fn(kind: Int, j: Int) -> String:
    if kind == LOW:
        return "rows_low" + String(j)
    if kind == HIGH:
        return "rows_high" + String(j)
    return "rows_middle"


def main() raises:
    var args = argv()
    if len(args) >= 7 and args[1] == "build":
        var d = Int(args[2])
        var eps = Int(args[3])
        var path = String(args[6]) + "/labels-d" + String(d) + "-eps" + String(eps) + ".txt"
        var workers = Int(args[7]) if len(args) > 7 else 4
        var batch = Int(args[8]) if len(args) > 8 else 16
        var added = extend_dataset(path, d, eps, members(d, eps, Int(args[4]), Int(args[5])), workers, batch)
        print("D_GAP_DATASET d=" + String(d), "eps=" + String(eps), "added", added, "file", path)
        return
    if (len(args) == 9 or len(args) == 10) and args[1] == "fit":
        var eps = Int(args[2])
        var dir = String(args[3])
        var d_lo = Int(args[4])
        var d_hi = Int(args[5])
        var jj = Int(args[6])
        var l_min = Int(args[7])
        var table = String()
        var mojo = String()
        var registry = String()
        var fitted = Dict[String, Int]()
        var regimes = List[List[Int]]()
        for j in range(jj):
            regimes.append([LOW, j, 0])
        for j in range(1, jj + 1):
            regimes.append([HIGH, j, 0])
        regimes.append([MIDDLE, jj, jj + 1])
        for reg in regimes:
            var found = False
            var last = RegimeFit()
            for d0 in range(d_lo, d_hi):
                var f = fit_regime(eps, reg[0], reg[1], reg[2], d0, d_hi, l_min, dir)
                if f.ok and f.gaps >= 2:
                    print("REGIME eps=" + String(eps), regime_name(reg[0], reg[1], reg[2]), "fit d>=" + String(d0),
                          "gaps", f.gaps, "samples", f.samples, "rows", len(f.rows), "rank", f.rank, "l>=" + String(l_min))
                    table += "T " + String(eps) + " " + String(reg[0]) + " " + String(reg[1]) + " " + String(reg[2]) + " " + String(d0) + " " + String(len(f.rows)) + "\n"
                    for row in f.rows:
                        var line = String("F")
                        for x in row:
                            line += " " + String(x)
                        table += line + "\n"
                    # Ray-row form: the fitted endpoints may depend on l only.
                    var d_floor = max(d0, reg[1] + reg[2]) if reg[0] == MIDDLE else d0
                    registry += "        List[Int]([" + String(eps) + ", " + String(reg[0]) + ", " + String(reg[1]) + ", " + String(reg[2]) + ", " + String(d_floor) + ", " + String(l_min) + "]),\n"
                    mojo += "\n\ndef " + regime_fn(reg[0], reg[1]) + "() -> List[List[Int]]:\n"
                    mojo += "    \"\"\"" + regime_name(reg[0], reg[1], reg[2]) + ", fitted on " + String(f.gaps) + " gaps d=" + String(d0) + ".." + String(d_hi) + ", " + String(f.samples) + " members, l>=" + String(l_min) + ". Rows: top,bottom,sum(w),w_y,k_lo l-slope,k_lo constant,k_hi l-slope,k_hi constant.\"\"\"\n"
                    mojo += "    return List[List[Int]]([\n"
                    var width = 5 if reg[0] == MIDDLE else 4
                    for row in f.rows:
                        # row = [top,bottom,s,y] + lo coefficients over [n, l, d, (r,) 1] + hi coefficients.
                        for e in range(2):
                            var o = 4 + e * width
                            if row[o] != 0 or row[o + 2] != 0 or (width == 5 and row[o + 3] != 0):
                                raise Error("fitted endpoint depends on n, d or r: not a ray-row table")
                        mojo += "        List[Int]([" + String(row[0]) + "," + String(row[1]) + "," + String(row[2]) + "," + String(row[3]) + ","
                        mojo += String(row[5]) + "," + String(row[4 + width - 1]) + "," + String(row[4 + width + 1]) + "," + String(row[4 + 2 * width - 1]) + "]),\n"
                    mojo += "    ])\n"
                    fitted[String(reg[0]) + ":" + String(reg[1])] = 1
                    found = True
                    break
                last = f^
            if not found:
                print("REGIME eps=" + String(eps), regime_name(reg[0], reg[1], reg[2]), "NO_FIT up to d=" + String(d_hi),
                      "last_reason:", last.reason)
        with open(String(args[8]), "w") as f:
            f.write(table)
        if len(args) == 10:
            var sign = "minus" if eps == -1 else "plus"
            var head = "\"\"\"Regime carrier rows of the class-A line (n+d, n, n" + ("+1" if eps == 1 else "-1") + "), every gap d >= d0.\n\n"
            head += "Generated by `kernel/class_a_gap_regimes.mojo fit " + String(eps) + " <labels> " + String(d_lo) + " " + String(d_hi) + " " + String(jj) + " " + String(l_min) + " ...` from the exact label\n"
            head += "datasets of evidence/class-a-gap-labels-2026-10-23/: for each residue regime, one\n"
            head += "l-affine table shared by every gap from its floor. A proof *target*: evidence only\n"
            head += "through `psc.class_a_gap_uniform.certify_regime_closure`. `regimes()` lists\n"
            head += "`[eps, kind, j, j1, d0, l_fit]` (kind 0 low r=j, 1 high r=d-j, 2 middle j<=r<=d-j1).\n"
            head += "Source note: docs/class-a-gap-uniform-certificate-design-2026-10-23.md.\n\"\"\"\n\n\n"
            head += "def regimes_" + sign + "() -> List[List[Int]]:\n    return List[List[Int]]([\n" + registry + "    ])\n"
            var dispatch = "\n\ndef rows_" + sign + "(kind: Int, j: Int) raises -> List[List[Int]]:\n"
            dispatch += "    \"\"\"Rows of the regime `(kind, j)` of this sign; an unfitted regime raises.\"\"\"\n"
            for reg in regimes:
                if (String(reg[0]) + ":" + String(reg[1])) in fitted:
                    dispatch += "    if kind == " + String(reg[0]) + " and j == " + String(reg[1]) + ":\n"
                    dispatch += "        return " + regime_fn(reg[0], reg[1]) + "()\n"
            dispatch += "    raise Error(\"no fitted regime rows for kind \" + String(kind) + \" j \" + String(j))\n"
            with open(String(args[9]), "w") as f:
                f.write(head + mojo + dispatch)
        return
    raise Error("usage: build D EPS LMIN LMAX DIR [WORKERS] [BATCH] | fit EPS DIR DMIN DMAX J LMIN OUT")
