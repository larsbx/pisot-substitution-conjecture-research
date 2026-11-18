"""(NM_V) decisions against an independent literal-word oracle."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_geometric_f import PrototileMap, PrototileState, StableRadiiCache
from psc.zero_fibre_asymptotes import Member, asymptotic, nmv_report

comptime RAY = 1500


def subst(sigma: List[List[Int]], w: List[Int]) -> List[Int]:
    var out = List[Int]()
    for x in w:
        for c in sigma[x]:
            out.append(c)
    return out^


def power(sigma: List[List[Int]], w: List[Int], k: Int) -> List[Int]:
    var out = w.copy()
    for _ in range(k):
        out = subst(sigma, out)
    return out^


def parikh(w: List[Int], n: Int) -> List[Int]:
    var p: List[Int] = [0, 0, 0]
    for i in range(n):
        p[w[i]] += 1
    return p^


def incidence_power(sigma: List[List[Int]], k: Int) -> List[List[Int]]:
    var cols = List[List[Int]]()
    for a in range(3):
        cols.append(parikh(power(sigma, [a], k), len(power(sigma, [a], k))))
    return cols^  # cols[a] = M^k e_a


def interior_ray(sigma: List[List[Int]], s: PrototileState, right: Bool) raises -> List[Int]:
    """Tiles from the central tile outward (rightward from its left end, or
    leftward from its left end), found from the literal address
    `σ^k(j) = P j S` with `(M^k − I) v = p(P)`; no `f`-map is used."""
    var v = s.vector()
    for k in range(1, 13):
        var img = power(sigma, [s.letter], k)
        var cols = incidence_power(sigma, k)
        var target = List[Int]()
        for i in range(3):
            target.append(cols[0][i] * v[0] + cols[1][i] * v[1] + cols[2][i] * v[2] - v[i])
        var found = -1
        for i in range(1, len(img) - 1):
            if img[i] == s.letter and parikh(img, i) == target:
                found = i
        if found < 0:
            continue
        var ray = List[Int]()
        if right:
            ray.append(s.letter)
            var seg = List[Int]()
            for i in range(found + 1, len(img)):
                seg.append(img[i])
            while len(ray) < RAY:
                for c in seg:
                    ray.append(c)
                seg = power(sigma, seg, k)
        else:
            var seg = List[Int]()
            for i in range(found):
                seg.append(img[i])
            while len(ray) < RAY:
                for i in range(len(seg) - 1, -1, -1):
                    ray.append(seg[i])
                seg = power(sigma, seg, k)
        return ray^
    raise Error("no literal interior address up to period 12")


def vertex_ray(sigma: List[List[Int]], letter: Int, right: Bool) -> List[Int]:
    var w: List[Int] = [letter]
    while len(w) < RAY:
        w = subst(sigma, w)
    # a periodic seam letter: take a power that fixes it
    for _ in range(6):
        var first = w[0] if right else w[len(w) - 1]
        if first == letter:
            break
        w = subst(sigma, w)
    var out = List[Int]()
    if right:
        for i in range(RAY):
            out.append(w[i])
    else:
        for i in range(RAY):
            out.append(w[len(w) - 1 - i])
    return out^


def literal_agree(a: List[Int], a_start: List[Int], b: List[Int], b_start: List[Int], right: Bool) raises -> Bool:
    """Do two rays share a vertex beyond which their next RAY/3 tiles agree?"""
    var sign = 1 if right else -1
    var va = Dict[String, Int]()
    var p = a_start.copy()
    for i in range(len(a)):
        if not right:
            p[a[i]] -= 1
        va[String(p[0], ",", p[1], ",", p[2])] = i
        if right:
            p[a[i]] += 1
    var q = b_start.copy()
    for i in range(len(b)):
        if not right:
            q[b[i]] -= 1
        var key = String(q[0], ",", q[1], ",", q[2])
        if key in va:
            var ia = va[key]
            var ok = True
            var span = 0
            # the tile after the shared vertex, in the direction of the ray
            var ja = ia if right else ia + 1
            var jb = i if right else i + 1
            while ja < len(a) and jb < len(b) and span < RAY // 3:
                if a[ja] != b[jb]:
                    ok = False
                    break
                ja += 1
                jb += 1
                span += 1
            if ok and span >= RAY // 3:
                return True
        if right:
            q[b[i]] += 1
    _ = sign
    return False


def literal_pair(sigma: List[List[Int]], seam_left: Int, seam_right: Int, s: PrototileState, right: Bool) raises -> Bool:
    var vr = vertex_ray(sigma, seam_right if right else seam_left, right)
    var ir = interior_ray(sigma, s, right)
    var start = s.vector()
    for i in range(3):
        start[i] = -start[i]
    return literal_agree(vr, [0, 0, 0], ir, start, right)


def check(sigma: List[List[Int]], members: Int, interior: Int, left: List[String], right: List[String]) raises:
    var boxes = StableRadiiCache()
    var m = PrototileMap(sigma)
    var r = nmv_report(m, boxes)
    print(sigma, "members", r.members, "interior", r.interior, "L", r.left_failures, "R", r.right_failures)
    assert_equal(r.members, members)
    assert_equal(r.interior, interior)
    assert_equal(r.left_failures, left)
    assert_equal(r.right_failures, right)


def main() raises:
    # Round-4 certificate: 1/012/21 merges an interior member on the right (g_R not injective).
    check([[1], [0, 1, 2], [2, 1]], 5, 1, [], ["1.2 ~R (1;-1,0,1)", "2.2 ~R (1;-1,0,1)"])
    assert_true(literal_pair([[1], [0, 1, 2], [2, 1]], 1, 2, PrototileState(1, -1, 0, 1), True))
    assert_true(literal_pair([[1], [0, 1, 2], [2, 1]], 2, 2, PrototileState(1, -1, 0, 1), True))
    # 01/12/021 fails on the right; 220/01/021 on the left (g not injective).
    check([[0, 1], [1, 2], [0, 2, 1]], 5, 1, [], ["1.0 ~R (2;-1,0,1)", "2.0 ~R (2;-1,0,1)"])
    assert_true(literal_pair([[0, 1], [1, 2], [0, 2, 1]], 1, 0, PrototileState(2, -1, 0, 1), True))
    check([[2, 2, 0], [0, 1], [0, 2, 1]], 9, 5, ["1.0 ~L (2;0,1,0)", "1.2 ~L (2;0,1,0)"], [])
    assert_true(literal_pair([[2, 2, 0], [0, 1], [0, 2, 1]], 1, 0, PrototileState(2, 0, 1, 0), False))
    # (NM_V) holds: 01/122/201 (the +1 seam control, beta_1 = 2) and Tribonacci.
    check([[0, 1], [1, 2, 2], [2, 0, 1]], 10, 4, [], [])
    check([[0, 1], [0, 2], [0]], 3, 0, [], [])
    # A decided non-asymptote is also literally non-agreeing on the sampled window.
    var sig: List[List[Int]] = [[0, 1], [1, 2, 2], [2, 0, 1]]
    var boxes = StableRadiiCache()
    var m = PrototileMap(sig)
    var v = Member(True, 1, 0, PrototileState(0, 0, 0, 0))
    var x = Member(False, -1, -1, PrototileState(1, 0, 1, -1))
    assert_false(asymptotic(m, v, x, True))
    assert_false(literal_pair(sig, 1, 0, PrototileState(1, 0, 1, -1), True))
    # Vertex members with a common left letter agree on the left half-line.
    var w = Member(True, 1, 1, PrototileState(1, 0, 0, 0))
    assert_true(asymptotic(m, v, w, False))
    _ = boxes
    require_contract("Zero-fibre asymptotes are decided exactly from left and right branches of the central overlap chain; (NM_V) failures on 1/012/21, 01/12/021 and 220/01/021 are replayed by independent literal word rays, (NM_V) holds on 01/122/201 and Tribonacci, and a decided non-asymptote shows no literal agreement.")
