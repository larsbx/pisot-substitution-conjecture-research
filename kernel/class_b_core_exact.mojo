"""Exact bounded core-closure labels: plus|minus GAP Q [CAP]."""
from std.sys import argv
from psc.class_b_core_exact import core_labels


def main() raises:
    var args = argv()
    if len(args) < 4 or len(args) > 5 or (args[1] != "plus" and args[1] != "minus"):
        raise Error("usage: plus|minus GAP Q [CAP]")
    var cap = Int(args[4]) if len(args) == 5 else 20000
    print(core_labels(args[1] == "plus", Int(args[2]), Int(args[3]), cap), end="")
