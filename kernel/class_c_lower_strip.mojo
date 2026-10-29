"""Reproducible class-C lower-strip partitions; refusals are not counterexamples."""
from std.sys import argv
from psc.class_c_lower_strip import certify_middle, domain_identities
from psc.class_c_tail_certificate import DIAGONAL, Piece, certify_piece, rows
from psc.class_c_gap_profile import c_block, frozen_onset


def main() raises:
    var a = argv()
    if len(a) == 2 and a[1] == "domain":
        print(domain_identities(1), end="")
        print(domain_identities(-1), end="")
        return
    if len(a) == 5 and a[1] == "middle":
        var eps = Int(a[2])
        var low = Int(a[3])
        var high = Int(a[4])
        var g = certify_middle(eps, low, high)
        print("MIDDLE eps=" + String(eps), "n>=3d+" + String(low), "n<=4d-" + String(high), "vertices", g.size(), "queries", g.queries, "polya", g.polya)
        print(rows(g), end="")
        return
    if len(a) == 5 and a[1] == "diagonal":
        var eps = Int(a[2])
        var c = Int(a[3])
        var d0 = Int(a[4])
        var g = certify_piece(Piece(eps, c, d0, 0, DIAGONAL))
        print("DIAGONAL eps=" + String(eps), "n=4d+" + String(c), "d>=" + String(d0), "vertices", g.size())
        print(rows(g), end="")
        return
    if len(a) == 4 and a[1] == "gap":
        var eps = Int(a[2])
        var d = Int(a[3])
        if d < 6 or d > 12 or (eps != 1 and eps != -1):
            raise Error("gap replay budget: 6<=d<=12, eps=+-1")
        var low = 2 * d + (-5 if eps == 1 else 1)
        for n in range(low, frozen_onset(d, eps)):
            var block = c_block(d, eps, n)
            if block.startswith("S "):
                raise Error("proposed domain member screened out")
            print("GAP eps=" + String(eps), "d=" + String(d), "n=" + String(n))
            print(block, end="", flush=True)
        return
    if len(a) == 3 and a[1] == "top-finite":
        var eps = Int(a[2])
        if eps != 1 and eps != -1:
            raise Error("class-C sign must be +-1")
        for d in range(6, 12):
            for j in range(1, 5):
                var n = frozen_onset(d, eps) - j
                var block = c_block(d, eps, n)
                if block.startswith("S "):
                    raise Error("top strip member screened out")
                print("TOP eps=" + String(eps), "d=" + String(d), "n=" + String(n))
                print(block, end="", flush=True)
        return
    raise Error("usage: domain | middle EPS A B | diagonal EPS C D0 | gap EPS D | top-finite EPS")
