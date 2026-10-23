"""Finite d=5 complete-graph calibration, including the plus n=0 endpoint.

This is not an infinite-ray certificate. Hard parameter budget n<=12.
"""
from std.sys import argv
from psc.class_a_line import ALine
from psc.class_a_line_graph import survey


def main() raises:
    var args = argv()
    if len(args) != 2:
        raise Error("usage: class_a_gap_five_probe.mojo EPS")
    var eps = Int(args[1])
    if eps != 1 and eps != -1:
        raise Error("class-A gap-five sign must be +1 or -1")
    var first = 0 if eps == 1 else 3
    for n in range(first, 13):
        _ = survey(ALine(5, eps, n % 5), n)
    print("CLASS_A_GAP_FIVE_FINITE", "eps=", eps, "first=", first,
          "last=12 whole_line_certified=false universal_139=false")
