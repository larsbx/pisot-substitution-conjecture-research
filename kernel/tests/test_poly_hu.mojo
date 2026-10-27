"""Bivariate integer polynomials in (h, u) and exact signs on the (u, t) box."""
from std.testing import assert_equal, assert_true
from finite_exact.rat_q import Q
from mojo_smoke.claims import require_contract
from psc.exact import q_sign
from psc.poly_hu import PolyHU, AffHU, elimination_hu, h_one_h, sign_on_box, sign_within_hull, box_polynomial


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
                var decided = False
                var s = 0
                try:
                    s = sign_on_box(f, 4, 6)
                    decided = True
                except:
                    pass
                # Assertion failures must not be caught as undecided signs.
                if decided and s != 0:
                    assert_true(g == 0 or g == s)
                    if g == s:
                        agreed += 1
    assert_true(agreed > 20)
    # A side condition restricts the box to where it is non-negative: 1 - 3u changes sign
    # on (0, 1/2) and refuses, but within the hull u <= 1/4 (side 1 - 4u) it is positive;
    # the complementary hull u >= 1/4 (side 4u - 1) keeps the sign change and refuses; the
    # zero side is no restriction; a hull that excludes the whole box refuses.
    assert_true(refuses(p([[1, -3]]), 2, 5))
    assert_equal(sign_within_hull(p([[1, -3]]), p([[1, -4]]), 2, 5), 1)
    var still = False
    try:
        _ = sign_within_hull(p([[1, -3]]), p([[-1, 4]]), 2, 5)
    except:
        still = True
    assert_true(still)
    assert_equal(sign_within_hull(p([[1, 1], [1, 0]]), PolyHU.zero(), 5, 5), 1)
    var empty = False
    try:
        _ = sign_within_hull(p([[1, 1]]), p([[-1]]), 5, 5)
    except:
        empty = True
    assert_true(empty)
    # The member hull E - l0 u (1+h) >= 0 is itself undecided on the box (its zero set
    # crosses the box). The margin 1 - 5u(1+h), positive at every member of l0 = 5 but
    # vanishing with the hull at the corner (u, t) -> (1/5, 0), is undecided on the box
    # and by cell skipping alone, and is certified by the hull multiple: it exceeds the
    # hull condition by h(1 + u + u h) > 0. Its negation certifies negative.
    var hull = elimination_hu(1).sub(PolyHU.monomial(0, 1, 5)).sub(PolyHU.monomial(1, 1, 5))
    assert_true(refuses(hull, 5, 5))
    var margin = p([[1, -5], [0, -5]])
    assert_true(refuses(margin, 5, 7))
    assert_equal(sign_within_hull(margin, hull, 5, 7), 1)
    assert_equal(sign_within_hull(margin.scale(-1), hull, 5, 7), -1)
    # A sign change inside the hull (1 - 6u vanishes at u = 1/6, reached by members with
    # l = 5) stays undecided: its h-free part is no multiple of the hull's.
    var oblique = p([[1, -6], [0, -5]])
    var undecided = False
    try:
        _ = sign_within_hull(oblique, hull, 5, 7)
    except:
        undecided = True
    assert_true(undecided)
    # 53^11 overflows signed Int64 despite floors <= 64. The generic
    # conversion must preserve the positive coefficient using exact powers.
    var high = PolyHU.const(1).add(PolyHU.monomial(11, 0, 1))
    var powers = box_polynomial(high, 1, 53)
    var expected = Q.one()
    for _ in range(11):
        expected = expected.div(Q(53, 1))
    assert_equal(q_sign(powers[11][11]), 1)
    assert_true(powers[11][11].eq(expected))
    # Wrapped denominator powers made this sign-changing polynomial certify positive.
    var false_positive = PolyHU.const(1).add(PolyHU.monomial(1, 0, -106)).add(PolyHU.monomial(2, 0, 2809)).add(PolyHU.monomial(11, 0, -1))
    assert_true(refuses(false_positive, 1, 53))
    var witness_h = Q(999999999999, 53000000000000)
    assert_equal(q_sign(evaluate(false_positive, witness_h, Q(999999999999, 1000000000000))), -1)
    # AffHU numerators: a + n b at r h = 0 has numerator a h(1+h) + E b.
    var m = AffHU(PolyHU.const(1), PolyHU.zero(), PolyHU.zero())
    assert_equal(m.numerator(PolyHU.zero(), 1), h_one_h())
    var mn = AffHU(PolyHU.zero(), PolyHU.const(1), PolyHU.zero())
    assert_equal(mn.numerator(PolyHU.zero(), -1), elimination_hu(-1))
    require_contract("integer polynomials in (h, u): ring laws; sign_on_box certifies exact signs on (0,1/l0) x (0,1/d0] via Bernstein subdivision on closed cells, agrees with rational grid samples, strips monomial factors, and refuses a sign change inside the box and a zero on the face t = 1/d0; sign_within_hull skips cells where a side condition is negative throughout and certifies within the hull what the box alone refuses, refuses when the sign change lies inside the hull or the hull is empty, and certifies through a non-negative hull multiple a margin that vanishes with the hull at the box corner; AffHU numerators realize a h(1+h) + E b + (r h) c h(1+h)")
