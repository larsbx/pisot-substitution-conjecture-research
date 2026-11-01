"""Class-C slope-three pieces. No aggregate verdict without all recorded pieces."""
from std.sys import argv
from psc.class_c_slope_three import GAP_SPLIT, SlopePlan, coverage_audit, refusal_controls, lower_line
from psc.class_c_lower_strip import certify_middle
from psc.class_c_tail_certificate import DIAGONAL, Piece, certify_piece, rows
from psc.class_c_gap_profile import c_block, frozen_onset


def main() raises:
    var args = argv()
    if len(args) == 2 and args[1] == "controls":
        print(refusal_controls(), end="")
        return
    if len(args) != 4:
        raise Error("usage: middle|diagonal|finite|coverage EPS A_OR_C")
    var mode = args[1]
    var eps = Int(args[2])
    var value = Int(args[3])
    if mode == "lower-line":
        if eps != -1:
            raise Error("lower-edge line budget is minus only")
        var g = lower_line(value)
        print("LOWER_LINE eps=-1 n=3d+" + String(value), "d>=24 vertices", g.size())
        print(rows(g), end="")
        return
    if mode == "diagonal":
        var p = SlopePlan(eps, 8)
        if value < p.diagonal_floor() or value > p.diagonal_last():
            raise Error("diagonal is outside this continuation's declared budget")
        var g = certify_piece(Piece(eps, value, GAP_SPLIT, 0, DIAGONAL))
        print("DIAGONAL eps=" + String(eps), "n=4d+" + String(value), "d>=" + String(GAP_SPLIT), "vertices", g.size())
        print(rows(g), end="")
        return
    var p = SlopePlan(eps, value)
    if mode == "middle":
        var g = certify_middle(eps, p.a, p.b)
        print("MIDDLE eps=" + String(eps), "n>=3d+" + String(p.a), "n<=4d-" + String(p.b), "vertices", g.size(), "queries", g.queries, "polya", g.polya)
        print(rows(g), end="")
        return
    if mode == "coverage":
        print(coverage_audit(p))
        return
    if mode == "finite":
        for d in range(6, GAP_SPLIT):
            for n in range(p.target(d), frozen_onset(d, eps)):
                var block = c_block(d, eps, n)
                if block.startswith("S "):
                    raise Error("slope-three finite end member screened out")
                print("END eps=" + String(eps), "d=" + String(d), "n=" + String(n))
                print(block, end="", flush=True)
        return
    raise Error("unknown slope-three mode")
