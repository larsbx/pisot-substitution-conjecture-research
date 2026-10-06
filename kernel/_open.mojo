from odd_letter_family_certificate import cover_shape, shape_family, NO_DELTA, Y, Z, O
from psc.pisot import is_pip
from psc.coincidence_formula import coincidence_level
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
def names(w: List[Int]) -> String:
    var n = List[String](["o","y","z"])
    var s = String("")
    for k in range(len(w)):
        s += n[w[k]]
    return s
def probe(l1: List[Int], l2: List[Int], s: Int, d: Int, tail: Bool) raises:
    var c = cover_shape(l1, l2, s, d, 5, tail, 5)
    print("open regions", c.open, flush=True)
    for r in range(len(c.open_forms)):
        ref f = c.open_forms[r]
        var m = len(f[0]) - 1
        var line = String("  forms:")
        for k in range(len(f)):
            line += " ["
            for j in range(len(f[k])):
                line += String(f[k][j]) + ","
            line += "]"
        print(line, flush=True)
        var pips = 0
        var tot = 0
        for t in range(6):
            var ns = List[Int](length=m, fill=t)
            var fam = shape_family(l1, l2, f)
            var sig = fam.instantiate(ns)
            var mt = Mat3(substitution_incidence(sig))
            var p = is_pip(mt)
            tot += 1
            if p:
                pips += 1
                print("    PIP member at", t, ":", names(sig[1]), names(sig[2]), flush=True)
                print("      level", coincidence_level(sig, O, Y), flush=True)
        print("    diagonal samples", tot, " PIP", pips)
def main() raises:
    probe(List[Int]([Z, Y]), List[Int]([Y, Z]), -1, -1, False)
    probe(List[Int]([Z, Y]), List[Int]([Y, Z]), -1, -2, False)
