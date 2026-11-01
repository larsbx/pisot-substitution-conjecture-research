"""Bounded arithmetic regression for the reconciled T_C / T_C2 cover.

The original certifier and receipts remain unchanged. This audit checks
assembly endpoints, not a graph or a universal PSC theorem.
"""
from psc.class_c_below_three import finite_start, finite_stop
from psc.class_c_lower_strip import check_sign


def mainline_piece(eps: Int, d: Int, n: Int) raises -> Int:
    check_sign(eps)
    if d < 6 or d > 64 or n < 0 or n > 400:
        raise Error("integration arithmetic audit budget: d=6..64, n=0..400")
    var a = 8 if eps == 1 else 16
    var b = 16 if eps == 1 else 8
    if 2 * n < 5 * d + a:
        return 0
    if n >= 3 * d:
        return 4 if n < 4 * d + (0 if eps == 1 else 4) else 5
    if d < 32:
        if n < finite_start(eps, d, 8) or n >= finite_stop(eps, d):
            raise Error("historical finite packet misses a new-cover member")
        return 1
    if n <= 3 * d - b:
        var u = 2 * n - 5 * d - a
        var v = 3 * d - n - b
        if u < 0 or v < 0 or d != a + 2 * b + u + 2 * v or n != 3 * a + 5 * b + 3 * u + 5 * v:
            raise Error("selected-sector inverse mismatch")
        return 2
    var c = n - 3 * d
    if c < 1 - b or c > -1 or d < a - 2 * c:
        raise Error("required bridge or frontier intersection mismatch")
    return 3


def mainline_coverage_audit(eps: Int) raises -> String:
    check_sign(eps)
    var counts = List[Int](length=6, fill=0)
    for d in range(6, 65):
        for n in range(401):
            counts[mainline_piece(eps, d, n)] += 1
    var out = "MAINLINE_COVER eps=" + String(eps) + " d=6..64 n=0..400"
    for k in range(6):
        out += " kind" + String(k) + "=" + String(counts[k])
    return out^
