"""Exact finite replay of the typed class-A carrier (not an all-n proof)."""
from std.sys import argv
from psc.class_a_typed_carrier import certify_finite


def main() raises:
    var args=argv()
    if len(args)>2:
        raise Error("usage: class_a_typed_carrier.mojo [n=18]")
    var n=18 if len(args)==1 else Int(args[1])
    _=certify_finite(n)
