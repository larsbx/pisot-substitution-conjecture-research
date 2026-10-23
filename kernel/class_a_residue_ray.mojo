"""Class-A residue rays (n+d, n, n+eps), n = d l + r: exact graphs, export, uniform certificate.

  mojo run -I . class_a_residue_ray.mojo survey D EPS LAST        # exact graphs n=1..LAST
  mojo run -I . class_a_residue_ray.mojo export D EPS N           # V/SEED/E/SUMMARY records
  mojo run -I . class_a_residue_ray.mojo certify D EPS R N0       # closure and descent, n>=N0, n=r mod d
  mojo run -I . class_a_residue_ray.mojo profile D EPS LAST       # per-residue vertex-count fit, n<=LAST
"""
from std.sys import argv
from psc.class_a_line import ALine
from psc.class_a_line_graph import survey, residue_profile
from psc.class_a_ray_tables import certify_ray


def main() raises:
    var args = argv()
    if len(args) < 5:
        raise Error("usage: survey D EPS LAST | export D EPS N | profile D EPS LAST | certify D EPS R N0")
    var d = Int(args[2])
    var eps = Int(args[3])
    if args[1] == "survey" and len(args) == 5:
        var last = Int(args[4])
        if last < 1 or last > 64:
            raise Error("complete-graph survey budget requires 1<=LAST<=64")
        for n in range(1, last + 1):
            var line = ALine(d, eps, n % d)
            if 2 * n + 6 * eps + 5 < d:
                continue   # outside the determinant-two PIP domain
            _ = survey(line, n)
        print("FINITE_SURVEY_COMPLETE line=" + ALine(d, eps, 0).line_name(), last, "universal_BH=false")
        return
    if args[1] == "export" and len(args) == 5:
        var n = Int(args[4])
        _ = survey(ALine(d, eps, n % d), n, True)
        return
    if args[1] == "profile" and len(args) == 5:
        var last = Int(args[4])
        if last < 1 or last > 64:
            raise Error("residue profile budget requires 1<=LAST<=64")
        _ = residue_profile(d, eps, last)
        return
    if args[1] == "certify" and len(args) == 6:
        _ = certify_ray(ALine(d, eps, Int(args[4])), Int(args[5]))
        return
    raise Error("usage: survey D EPS LAST | export D EPS N | profile D EPS LAST | certify D EPS R N0")
