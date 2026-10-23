"""Uniform class-A carrier closure and descent certificate.

  mojo run -I . class_a_carrier_closure.mojo [n0=8]
"""
from std.sys import argv
from psc.class_a_carrier_closure import certify_closure
from psc.class_a_carrier_descent import certify_descent


def main() raises:
    var args = argv()
    if len(args) > 2:
        raise Error("usage: class_a_carrier_closure.mojo [n0=8]")
    var n0 = 8 if len(args) == 1 else Int(args[1])
    _ = certify_closure(n0)
    _ = certify_descent(n0)
    print("CLASS_A_LINE_BOUNDARY_HITTING n>=" + String(n0), "closure=true descent=true universal_139=false")
