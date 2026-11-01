"""Below-three class-C pieces; a refused proposal is not a BH counterexample."""
from std.sys import argv
from psc.class_c_below_three import LINE_FLOOR, certify_line, certify_sector, finite_start, finite_stop, coverage_audit, target_line_floor
from psc.class_c_tail_certificate import rows
from psc.class_c_gap_profile import c_block, rows_of, vertices_of


def main() raises:
    var args = argv()
    if len(args) == 5 and args[1] == "shifted-line":
        var eps = Int(args[2])
        var c = Int(args[3])
        var floor = Int(args[4])
        var g = certify_line(eps, c, floor)
        print("SHIFTED_LINE eps=" + String(eps), "n-3d=" + String(c), "d>=" + String(floor), "vertices", g.size())
        print(rows(g), end="")
        return
    if len(args) == 6 and args[1] == "exceptions":
        var eps = Int(args[2])
        var c = Int(args[3])
        var lo = Int(args[4])
        var hi = Int(args[5])
        if (eps != 1 and eps != -1) or c < -15 or c > (3 if eps == 1 else 5) or lo < 32 or hi > 47 or lo > hi:
            raise Error("exception budget: legal line, 32<=lo<=hi<=47")
        for d in range(lo, hi + 1):
            var n = 3 * d + c
            var block = c_block(d, eps, n)
            if block.startswith("S "):
                raise Error("exception member screened outside PIP domain")
            print("EXCEPTION eps=" + String(eps), "d=" + String(d), "n=" + String(n))
            print(block, end="", flush=True)
        return
    if len(args) == 5 and args[1] == "target-line":
        var eps = Int(args[2])
        var c = Int(args[3])
        var a = Int(args[4])
        var floor = target_line_floor(c, a)
        var g = certify_line(eps, c, floor)
        print("TARGET_LINE eps=" + String(eps), "n-3d=" + String(c), "a=" + String(a), "d>=" + String(floor), "vertices", g.size())
        print(rows(g), end="")
        return
    if len(args) == 5 and args[1] == "coverage":
        print(coverage_audit(Int(args[2]), Int(args[3]), Int(args[4])))
        return
    if len(args) == 4 and args[1] == "control":
        var eps = Int(args[2])
        var a = Int(args[3])
        if (eps != 1 and eps != -1) or (a != 8 and a != 16) or (eps == -1 and a != 8):
            raise Error("label-control budget: plus a=8/16, minus a=8")
        var ds = List[Int]([a + 16, a + 36]) if eps == 1 else List[Int]([40, 40])
        var ns = List[Int]([3 * a + 40, 3 * a + 90]) if eps == 1 else List[Int]([112, 116])
        var prior = String()
        var sizes = List[Int]()
        for i in range(2):
            var block = c_block(ds[i], eps, ns[i])
            if block.startswith("S "):
                raise Error("label control is outside the PIP domain")
            sizes.append(vertices_of(block))
            var these = rows_of(block)
            if i == 0:
                prior = these
            elif these == prior:
                raise Error("proposed label mismatch was not reproduced")
            print("MEMBER eps=" + String(eps), "d=" + String(ds[i]), "n=" + String(ns[i]))
            print(block, end="")
        print("LABEL_MISMATCH eps=" + String(eps), "a=" + String(a), "vertices", sizes[0], sizes[1])
        return
    if len(args) == 5 and args[1] == "sector":
        var eps = Int(args[2])
        var a = Int(args[3])
        var b = Int(args[4])
        var g = certify_sector(eps, a, b)
        print("SECTOR eps=" + String(eps), "2n-5d>=" + String(a), "3d-n>=" + String(b), "vertices", g.size(), "queries", g.queries, "polya", g.polya)
        print(rows(g), end="")
        return
    if len(args) == 4 and args[1] == "line":
        var eps = Int(args[2])
        var c = Int(args[3])
        var g = certify_line(eps, c)
        print("LINE eps=" + String(eps), "n-3d=" + String(c), "d>=" + String(LINE_FLOOR), "vertices", g.size())
        print(rows(g), end="")
        return
    if len(args) == 4 and args[1] == "finite":
        var eps = Int(args[2])
        var a = Int(args[3])
        for d in range(6, LINE_FLOOR):
            for n in range(finite_start(eps, d, a), finite_stop(eps, d)):
                var block = c_block(d, eps, n)
                if block.startswith("S "):
                    raise Error("finite end member screened outside PIP domain")
                print("END eps=" + String(eps), "a=" + String(a), "d=" + String(d), "n=" + String(n))
                print(block, end="", flush=True)
        return
    if len(args) == 5 and args[1] == "member":
        var eps = Int(args[2])
        var d = Int(args[3])
        var n = Int(args[4])
        print("MEMBER eps=" + String(eps), "d=" + String(d), "n=" + String(n))
        var block = c_block(d, eps, n)
        if block.startswith("S "):
            raise Error("control member not PIP")
        print(block, end="")
        return
    raise Error("usage: sector|coverage EPS A B | line EPS C | target-line EPS C A | shifted-line EPS C FLOOR | exceptions EPS C LO HI | finite EPS A | member EPS D N | control EPS A")
