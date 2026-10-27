"""Compare three finite canonical exports, including all typed interval ends."""
from std.sys import argv
from psc.class_b_label_fit import read_intervals, affine_equal, tail_partition_ok


def main() raises:
    var args = argv()
    if len(args) != 5:
        raise Error("usage: FILE_L FILE_L1 FILE_LSTEP STEP")
    var a = read_intervals(String(args[1]))
    var b = read_intervals(String(args[2]))
    var c = read_intervals(String(args[3]))
    if not tail_partition_ok(a, b) or not affine_equal(a, b, c, Int(String(args[4]))):
        raise Error("FINITE_LABEL_FIT_REFUSED")
    print("FINITE_LABEL_FIT_PASS rows", len(a), "step", Int(String(args[4])))
