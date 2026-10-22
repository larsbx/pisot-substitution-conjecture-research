"""Certify both omitted strips, or one explicitly selected component."""
from std.sys import argv
from psc.class_d_minus_boundary_strips import certify_minus_strip, certify_minus_strips


def main() raises:
    var args = argv()
    if len(args) == 1:
        _ = certify_minus_strips()
    elif len(args) == 2 and (args[1] == "0" or args[1] == "1"):
        _ = certify_minus_strip(Int(args[1]))
    else:
        raise Error("usage: class_d_minus_boundary_strips [0|1]")
