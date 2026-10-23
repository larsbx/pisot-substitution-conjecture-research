"""Bivariate integer polynomials in (h, u) and exact signs on the (u, t) box."""
from std.testing import assert_equal, assert_true
from finite_exact.rat_q import Q
from mojo_smoke.claims import require_contract
from psc.exact import q_sign
from psc.poly_hu import PolyHU, AffHU, elimination_hu, h_one_h, sign_on_box


def p(coeffs: List[List[Int]]) -> PolyHU:
    var out = PolyHU.zero()
    for i in range(len(coeffs)):
        for j in range(len(coeffs[i])):
            out = out.add(PolyHU.monomial(i, j, coeffs[i][j]))
    return out^


def evaluate(f: PolyHU, h: Q, u: Q) -> Q:
    var total = Q.zero()
    for i in range(len(f.c)):
        for j in range(len(f.c[i])):
            if f.c[i][j] == 0:
                continue
            var term = Q.from_int(Int64(f.c[i][j]))
            for _ in range(i):
                term = term.mul(h)
            for _ in range(j):
                term = term.mul(u)
            total = total.add(term)
    return total^


def refuses(f: PolyHU, l0: Int, d0: Int) -> Bool:
    try:
        _ = sign_on_box(f, l0, d0)
    except:
        return True
    return False


def grid_sign(f: PolyHU, l0: Int, d0: Int) -> Int:
    """Sign of `f(u t, u)` on a rational grid inside `(0, 1/l0) x (0, 1/d0]`: `+-1`
    when every sampled sign agrees, `0` otherwise."""
    var seen = 0
    for a in range(1, 8):
        for b in range(1, 9):
            var u = Q(Int64(a), Int64(8 * l0))
            var t = Q(Int64(b), Int64(8 * d0))
            var s = q_sign(evaluate(f, u.mul(t), u))
            if s == 0:
                return 0
            if seen == 0:
                seen = s
            elif seen != s:
                return 0
    return seen


def main() raises:
    # Ring laws on small polynomials.
    var a = p([[1, 2], [3, 0]])          # 1 + 2u + 3h
    var b = p([[0, 1], [1, 1]])          # u + h + h u
    assert_equal(a.add(b).sub(b), a)
    assert_equal(a.mul(b), b.mul(a))
    assert_equal(a.mul(b.add(a)), a.mul(b).add(a.mul(a)))
    assert_true(a.sub(a).is_zero())
    assert_equal(PolyHU.monomial(2, 1, 5).deg_h(), 2)
    assert_equal(PolyHU.monomial(2, 1, 5).deg_u(), 1)
    # Known signs on the box.
    assert_equal(sign_on_box(p([[1, 1], [1, 0]]), 5, 5), 1)                 # 1 + u + h
    assert_equal(sign_on_box(p([[-1, 1]]), 5, 5), -1)                         # u - 1 < 0 since u < 1/5
    assert_equal(sign_on_box(PolyHU.monomial(1, 0, 1), 5, 5), 1)             # h > 0 after stripping
    assert_equal(sign_on_box(PolyHU.zero(), 5, 5), 0)
    assert_equal(sign_on_box(elimination_hu(1), 5, 5), 1)                    # n h(1+h) > 0
    assert_equal(sign_on_box(elimination_hu(-1), 5, 5), 1)
    assert_equal(sign_on_box(h_one_h(), 3, 3), 1)
    # A sign change inside the box refuses; a zero exactly on the face t = 1/d0 refuses.
    assert_true(refuses(p([[-1, 10]]), 5, 5))                                 # 10u - 1 changes sign at u = 1/10
    assert_true(refuses(p([[0, -1], [5, 0]]), 5, 5))                          # 5h - u = u(5t - 1) vanishes at t = 1/5
    assert_true(refuses(p([[0, -1], [6, 0]]), 5, 5))                          # 6h - u = u(6t - 1) changes sign: t reaches 1/5 > 1/6
    assert_equal(sign_on_box(p([[0, -1], [4, 0]]), 5, 5), -1)                 # 4h - u = u(4t - 1) < 0 since t <= 1/5
    # Agreement with a rational grid for a family of polynomials.
    var agreed = 0
    for c0 in range(-3, 4):
        for c1 in range(-3, 4, 2):
            for c2 in range(-2, 3):
                var f = p([[c0, c1], [c2, 0], [0, 1]])   # c0 + c1 u + c2 h + h^2 u
                var g = grid_sign(f, 4, 6)
                try:
                    var s = sign_on_box(f, 4, 6)
                    if s != 0:
                        assert_true(g == 0 or g == s)
                        if g == s:
                            agreed += 1
                except:
                    pass
    assert_true(agreed > 20)
    # AffHU numerators: a + n b at r h = 0 has numerator a h(1+h) + E b.
    var m = AffHU(PolyHU.const(1), PolyHU.zero(), PolyHU.zero())
    assert_equal(m.numerator(PolyHU.zero(), 1), h_one_h())
    var mn = AffHU(PolyHU.zero(), PolyHU.const(1), PolyHU.zero())
    assert_equal(mn.numerator(PolyHU.zero(), -1), elimination_hu(-1))
    require_contract("integer polynomials in (h, u): ring laws; sign_on_box certifies exact signs on (0,1/l0) x (0,1/d0] via Bernstein subdivision on closed cells, agrees with rational grid samples, strips monomial factors, and refuses a sign change inside the box and a zero on the face t = 1/d0; AffHU numerators realize a h(1+h) + E b + (r h) c h(1+h)")
