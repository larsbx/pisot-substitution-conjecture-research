"""Class-A gaps d>=5, both signs: boundary hitting for every n = d l + r with l >= L0.

  mojo run -I . class_a_gap_theorem.mojo cover EPS DMAX       # residue coverage of every gap 5<=d<=DMAX and the eventual pattern
  mojo run -I . class_a_gap_theorem.mojo certify EPS L0       # the assembled theorem for one sign
  mojo run -I . class_a_gap_theorem.mojo certify-all L0       # both signs
"""
from std.sys import argv
from psc.class_a_gap_theorem import certify_gap_theorem, eventual_cover, residue_cover, FIRST_GAP
from psc.class_a_gap_regime_tables import fitted_regimes, regime_of
from psc.class_a_ray_tables import tabulated_rays


def print_cover(eps: Int, d_max: Int) raises:
    var from_d = eventual_cover(eps)
    var specs = fitted_regimes()
    var rays = tabulated_rays()
    for d in range(FIRST_GAP, d_max + 1):
        var cover = residue_cover(eps, d)
        var line = String("CLASS_A_GAP_COVER eps=") + String(eps) + " d=" + String(d) + ":"
        for r in range(d):
            var c = cover[r]
            if c >= 0:
                line += " r" + String(r) + "=" + regime_of(specs[c], 1).name()
            else:
                line += " r" + String(r) + "=ray(n0=" + String(rays[-2 - c][3]) + ")"
        print(line)
    print("CLASS_A_GAP_COVER_EVENTUAL eps=" + String(eps), "regimes_cover_every_residue_from_d>=" + String(from_d))


def main() raises:
    var args = argv()
    if len(args) == 4 and args[1] == "cover":
        print_cover(Int(args[2]), Int(args[3]))
        return
    if len(args) == 4 and args[1] == "certify":
        _ = certify_gap_theorem(Int(args[2]), Int(args[3]))
        return
    if len(args) == 3 and args[1] == "certify-all":
        for eps in [-1, 1]:
            _ = certify_gap_theorem(eps, Int(args[2]))
        return
    raise Error("usage: cover EPS DMAX | certify EPS L0 | certify-all L0")
