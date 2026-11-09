"""Negative controls for Open Problem Concentration (docs/c4-concentration-attack-2026-11-06.md).

1. A single irreducible 2-binomially-equivalent pair can put a nonzero K3 into the
   determinant sector of a PIP incidence matrix, so the degree-three case of
   Concentration cannot be closed pair by pair: T13 and M0.
2. The reduction "b2 = p implies Concentration" is not a general route: the PIP
   substitution 011/2/120 has distinct 2-binomially equivalent factors of length 7.
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.words import Pair, k2, k3, parikh


def _digits(s: String) -> List[Int]:
    var out = List[Int]()
    for c in s.codepoints():
        out.append(Int(c.to_u32()) - 48)
    return out^


def _is_irreducible(u: List[Int], v: List[Int]) -> Bool:
    var pu: List[Int] = [0, 0, 0]
    var pv: List[Int] = [0, 0, 0]
    for i in range(len(u) - 1):
        pu[u[i]] += 1
        pv[v[i]] += 1
        if pu[0] == pv[0] and pu[1] == pv[1] and pu[2] == pv[2]:
            return False
    return True


def _chi(m: List[Int], x: Int) -> Int:
    """det(x I - M) for a row-major 3x3 integer matrix."""
    var a = x - m[0]
    var e = x - m[4]
    var i = x - m[8]
    var b = -m[1]
    var c = -m[2]
    var d = -m[3]
    var f = -m[5]
    var g = -m[6]
    var h = -m[7]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def test_degree3_det_sector_pair() raises:
    var u = _digits("1222200110120")
    var v = _digits("2201121220001")
    var p = Pair(u, v)
    assert_equal(parikh(u), parikh(v))
    assert_true(_is_irreducible(u, v))
    var z2 = k2(p)
    for x in z2:
        assert_equal(x, 0)
    var z3 = k3(p)
    var nonzero = False
    for x in z3:
        if x != 0:
            nonzero = True
    assert_true(nonzero)
    # M0, row-major; primitive (all entries positive)
    var m: List[Int] = [5, 21, 1, 6, 26, 1, 6, 24, 1]
    for x in m:
        assert_true(x > 0)
    var det = -_chi(m, 0)
    assert_equal(det, -2)
    # chi = x^3 - 32x^2 + 5x + 2: no rational root (+-1, +-2), so irreducible;
    # sign changes at -1, 0, 1, 32 give two roots in (-1, 1) and one > 1: Pisot.
    for r in [1, -1, 2, -2]:
        assert_true(_chi(m, r) != 0)
    assert_true(_chi(m, -1) < 0 and _chi(m, 0) > 0 and _chi(m, 1) < 0 and _chi(m, 32) > 0)
    # M0^{(x)3} K3 = det(M0) K3: K3 lies in the determinant sector
    for a in range(3):
        for b in range(3):
            for c in range(3):
                var s = 0
                for x in range(3):
                    for y in range(3):
                        for w in range(3):
                            s += m[3 * a + x] * m[3 * b + y] * m[3 * c + w] * z3[9 * x + 3 * y + w]
                assert_equal(s, det * z3[9 * a + 3 * b + c])


def test_two_binomially_equivalent_factors() raises:
    var sigma: List[List[Int]] = [[0, 1, 1], [2], [1, 2, 0]]
    var w: List[Int] = [0]
    for _ in range(6):
        var nxt = List[Int]()
        for a in w:
            for b in sigma[a]:
                nxt.append(b)
        w = nxt^
    var x = _digits("0112201")
    var y = _digits("1200112")
    var found_x = False
    var found_y = False
    for i in range(len(w) - 6):
        var mx = True
        var my = True
        for j in range(7):
            if w[i + j] != x[j]:
                mx = False
            if w[i + j] != y[j]:
                my = False
        found_x = found_x or mx
        found_y = found_y or my
    assert_true(found_x and found_y)
    var z2 = k2(Pair(x, y))
    for t in z2:
        assert_equal(t, 0)
    assert_false(x == y)


def main() raises:
    test_degree3_det_sector_pair()
    test_two_binomially_equivalent_factors()
    print("Concentration controls: T13 puts K3 in the det sector of PIP M0 (det -2); 011/2/120 has 2-binomially equivalent factors 0112201 ~ 1200112.")
    require_contract("Concentration negative controls: the irreducible 2-binomially equivalent pair (1222200110120, 2201121220001) has nonzero K3 with M0^{(x)3} K3 = det(M0) K3 for the primitive irreducible Pisot M0 = [[5,21,1],[6,26,1],[6,24,1]] (det -2), so the degree-three det-sector condition holds for a single pair; and the PIP substitution 011/2/120 has distinct 2-binomially equivalent factors 0112201 and 1200112 of its fixed-point iterate sigma^6(0)")
