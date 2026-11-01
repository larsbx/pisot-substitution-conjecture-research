"""Uniform middle-row membership only; no closure, descent or BH claim."""
from std.sys import argv
from psc.class_b_middle_geometry import certify_middle_members, certify_middle_core, certify_middle_closure, certify_middle_descent


def main() raises:
    var args = argv()
    var l0 = Int(args[1]) if len(args) > 1 else 4
    if len(args) > 2 and args[2] == "descent-floors":
        for eps in [-1, 1]:
            var accepted = False
            for g0 in range(12 if eps == -1 else 16, 33):
                try:
                    var st = certify_middle_descent(eps, l0, False, g0)
                    print("CLASS_B_MIDDLE_DESCENT_ACCEPT eps", eps, "g0", g0, "l0", l0, "stats", st)
                    accepted = True
                    break
                except err:
                    print("CLASS_B_MIDDLE_DESCENT_REFUSE eps", eps, "g0", g0, String(err))
            if not accepted:
                raise Error("no middle descent certificate floor through 32")
        return
    if len(args) > 2 and args[2] == "descent":
        for eps in [-1, 1]:
            print("CLASS_B_MIDDLE_DESCENT eps", eps, "stats", certify_middle_descent(eps, l0))
        return
    if len(args) > 2 and args[2] == "closure":
        for eps in [-1, 1]:
            print("CLASS_B_MIDDLE_CLOSURE eps", eps, "checks", certify_middle_closure(eps, l0))
        return
    for eps in [-1, 1]:
        print("CLASS_B_MIDDLE_CORE eps", eps, "l0", l0, "strict_labels", certify_middle_core(eps, l0), "closed=false")
        print("CLASS_B_MIDDLE_MEMBERS eps", eps, "l0", l0, "rows", certify_middle_members(eps, l0), "closure=false descent=false BH=false")
