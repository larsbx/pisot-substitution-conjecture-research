"""Class-A gaps d>=5: resumable exact label datasets and their regime fits.

  mojo run -I . class_a_gap_regimes.mojo build D EPS LMIN LMAX DIR [WORKERS] [BATCH]
      members n = d l + r, LMIN <= l <= LMAX, of (n+d,n,n+eps); appends to
      DIR/labels-dD-epsE.txt, skipping members already recorded
  mojo run -I . class_a_gap_regimes.mojo fit EPS DIR DMIN DMAX J LMIN OUT
      for regimes low r=0..J-1, high r=d-1..d-J and middle J<=r<=d-J-1, the
      least gap d0 >= DMIN from which one fit holds for all d0<=d<=DMAX;
      fitted tables go to OUT
"""
from std.sys import argv
from psc.class_a_gap_dataset import extend_dataset, members
from psc.class_a_gap_regimes import LOW, HIGH, MIDDLE, RegimeFit, fit_regime, regime_name


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
    if len(args) == 9 and args[1] == "fit":
        var eps = Int(args[2])
        var dir = String(args[3])
        var d_lo = Int(args[4])
        var d_hi = Int(args[5])
        var jj = Int(args[6])
        var l_min = Int(args[7])
        var table = String()
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
                    found = True
                    break
                last = f^
            if not found:
                print("REGIME eps=" + String(eps), regime_name(reg[0], reg[1], reg[2]), "NO_FIT up to d=" + String(d_hi),
                      "last_reason:", last.reason)
        with open(String(args[8]), "w") as f:
            f.write(table)
        return
    raise Error("usage: build D EPS LMIN LMAX DIR [WORKERS] [BATCH] | fit EPS DIR DMIN DMAX J LMIN OUT")
