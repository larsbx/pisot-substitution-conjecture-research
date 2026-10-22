"""Class-A minus line (n+1,n,n-1): complete finite graphs, export, uniform certificate.

  mojo run -I . class_a_minus_line.mojo survey LAST    # exact graphs n=1..LAST
  mojo run -I . class_a_minus_line.mojo export N       # V/SEED/E/SUMMARY records
  mojo run -I . class_a_minus_line.mojo certify [n0]   # closure and descent for n>=n0
"""
from std.sys import argv
from psc.class_a_line import minus_line
from psc.class_a_line_graph import survey
from psc.class_a_minus_carrier import minus_rows
from psc.class_a_minus_descent_data import minus_piece_rows, minus_descent_rows
from psc.class_a_carrier_closure import certify_closure_line
from psc.class_a_carrier_descent import certify_descent_line


def main() raises:
    var args = argv()
    if len(args) < 2 or len(args) > 3:
        raise Error("usage: survey LAST | export N | certify [n0]")
    var line = minus_line()
    if args[1] == "survey" and len(args) == 3:
        var last = Int(args[2])
        if last < 1 or last > 64:
            raise Error("complete-graph survey budget requires 1<=LAST<=64")
        for n in range(1, last + 1):
            _ = survey(line, n)
        print("FINITE_SURVEY_COMPLETE line=" + line.name(), last, "universal_BH=false")
        return
    if args[1] == "export" and len(args) == 3:
        _ = survey(line, Int(args[2]), True)
        return
    if args[1] == "certify":
        var n0 = 10 if len(args) == 2 else Int(args[2])
        _ = certify_closure_line(line, n0, minus_rows())
        _ = certify_descent_line(line, n0, minus_rows(), minus_piece_rows(), minus_descent_rows())
        print("CLASS_A_LINE_BOUNDARY_HITTING n>=" + String(n0), "line=" + line.name(),
              "closure=true descent=true universal_139=false")
        return
    raise Error("usage: survey LAST | export N | certify [n0]")
