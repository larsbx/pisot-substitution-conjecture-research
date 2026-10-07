"""Exact regressions for the polynomial line mode (psc.poly_line).

docs/p1a-a1-prime-2026-10-05.md §3l. Polynomial arithmetic against
evaluation, the polynomial prover's soundness under assumptions, and
agreement with the affine line verifier wherever both apply.
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.cone_witness import ConeFamily, Prover, aff_eval, search_witness_line, verify_witness_line
from psc.poly_line import (
    Poly,
    PolyStep,
    poly_add,
    poly_const,
    poly_degree,
    poly_eval,
    poly_from_aff,
    mono_var,
    poly_mul,
    poly_scale,
    poly_nonneg_under,
    poly_steps,
    poly_sub,
    poly_vanishes_under,
    enumerate_point_paths,
    solve_lift,
    steps_at,
    verify_witness_poly,
)
from psc.product_lift import ProductLift, lift_affine, lift_form, lift_point, mccormick_forms, product_lift_of
from odd_letter_family_certificate import O, Y, Z, shape_family


def _forms(c_lo: Int, c_hi: Int, a: Int, m: Int) -> List[List[Int]]:
    """Every affine form over m variables with constant in c_lo..c_hi and
    coefficients in -a..a."""
    var out = List[List[Int]]()
    var span = 2 * a + 1
    var count = 1
    for _ in range(m):
        count *= span
    for c in range(c_lo, c_hi + 1):
        for code in range(count):
            var f = List[Int]([c])
            var r = code
            for _ in range(m):
                f.append(r % span - a)
                r //= span
            out.append(f^)
    return out^


def test_polynomial_arithmetic_matches_evaluation() raises:
    """For a stride of affine forms a, b, c over three variables, P = a b + c
    and Q = P a evaluate as the products do at every point of [0, 3]^3, with
    degrees at most 2 and 3."""
    var forms = _forms(-2, 2, 1, 3)
    var n = len(forms)
    var checked = 0
    for i in range(0, n, 7):
        for j in range(i, n, 11):
            var k = (i + 3 * j) % n
            var a = poly_from_aff(forms[i])
            var p = poly_add(poly_mul(a, poly_from_aff(forms[j])), poly_from_aff(forms[k]))
            var q = poly_mul(p, a)
            assert_true(poly_degree(p) <= 2)
            assert_true(poly_degree(q) <= 3)
            for x in range(4):
                for y in range(4):
                    for z in range(4):
                        var ns = List[Int]([x, y, z])
                        var va = aff_eval(forms[i], ns)
                        var vp = va * aff_eval(forms[j], ns) + aff_eval(forms[k], ns)
                        assert_equal(poly_eval(p, ns), vp)
                        assert_equal(poly_eval(q, ns), vp * va)
                        assert_equal(poly_eval(poly_sub(p, p), ns), 0)
            checked += 1
    assert_true(checked > 100)


def test_polynomial_prover_is_sound() raises:
    """Whenever poly_nonneg_under proves P = U V + W >= 0 or P U >= 0 under
    one or two assumptions with coefficients in -1..1, P is >= 0 at every
    point of [0, 5]^2 where they hold; it proves some, and vanishing needs
    both signs."""
    var assume = _forms(-1, 1, 1, 2)
    var targets = _forms(-2, 2, 2, 2)
    var proved = 0
    for i in range(len(assume)):
        for j in range(i, len(assume)):
            var pv = Prover(List[List[Int]]([assume[i].copy(), assume[j].copy()]))
            for k in range(0, len(targets), 3):
                var u = poly_from_aff(assume[i])
                var p = poly_add(poly_mul(u, poly_from_aff(targets[k])), poly_from_aff(targets[(7 * k + 3) % len(targets)]))
                var r = poly_mul(p, u)
                var ok_p = poly_nonneg_under(p, pv)
                var ok_r = poly_nonneg_under(r, pv)
                if ok_p:
                    proved += 1
                for x in range(6):
                    for y in range(6):
                        var ns = List[Int]([x, y])
                        if aff_eval(assume[i], ns) < 0 or aff_eval(assume[j], ns) < 0:
                            continue
                        if ok_p:
                            assert_true(poly_eval(p, ns) >= 0)
                        if ok_r:
                            assert_true(poly_eval(r, ns) >= 0)
    assert_true(proved > 1000)
    var a = List[Int]([-3, 2, -4])
    assert_true(poly_vanishes_under(poly_from_aff(a), Prover(List[List[Int]]([a.copy(), List[Int]([3, -2, 4])]))))
    assert_false(poly_vanishes_under(poly_from_aff(a), Prover(List[List[Int]]([a.copy()]))))


def test_polynomial_mode_agrees_with_line_mode() raises:
    """On the line-mode family (z^a y^b, y^(b+1) z^(a+1)), a = b + 2 + n1,
    b = 2 + n2, the line path verifies in polynomial mode too, every
    single-offset perturbation that line mode rejects is rejected, and the
    path instantiated at points of [0, 4]^2 verifies on the point family."""
    var subst = List[List[Int]]()
    subst.append(List[Int]([3, 1, 1]))
    subst.append(List[Int]([1, 0, 1]))
    subst.append(List[Int]([2, 0, 1]))
    subst.append(List[Int]([4, 1, 1]))
    var fam = shape_family(List[Int]([Z, Y]), List[Int]([Y, Z]), subst)
    var w = search_witness_line(fam, O, Y, 3, 6, Y, Z)
    assert_true(w.found)
    assert_true(verify_witness_line(fam, O, Y, w.steps))
    var ps = poly_steps(w.steps)
    assert_true(verify_witness_poly(fam, O, Y, ps, Prover()))
    var rejected = 0
    for l in range(len(ps)):
        for side in range(2):
            var bent = w.steps.copy()
            if side == 0:
                bent[l].off_a[0] += 1
            else:
                bent[l].off_b[0] += 1
            var line_ok = verify_witness_line(fam, O, Y, bent)
            assert_equal(verify_witness_poly(fam, O, Y, poly_steps(bent), Prover()), line_ok)
            if not line_ok:
                rejected += 1
    assert_true(rejected >= 1)
    for n1 in range(5):
        for n2 in range(5):
            var ns = List[Int]([n1, n2])
            var at = List[List[Int]]()
            for k in range(len(subst)):
                at.append(List[Int]([aff_eval(subst[k], ns)]))
            var point = shape_family(List[Int]([Z, Y]), List[Int]([Y, Z]), at)
            assert_true(verify_witness_line(point, O, Y, steps_at(ps, ns)))


def _line_family_at(ns: List[Int]) raises -> ConeFamily:
    var subst = List[List[Int]]()
    subst.append(List[Int]([3 + ns[0] + ns[1]]))
    subst.append(List[Int]([1 + ns[1]]))
    subst.append(List[Int]([2 + ns[1]]))
    subst.append(List[Int]([4 + ns[0] + ns[1]]))
    return shape_family(List[Int]([Z, Y]), List[Int]([Y, Z]), subst)


def test_linear_lift_solves_point_paths() raises:
    """On the line-mode family, at the base points (1, 2) and (2, 1): every
    enumerated point path verifies on the point family, and some solves
    (solve_lift) to a polynomial path whose end offset is zero and which
    verify_witness_poly accepts on the region its offset bounds carve; the
    solved path, instantiated at every point of [0, 5]^2 inside that region,
    verifies on the point family."""
    var subst = List[List[Int]]()
    subst.append(List[Int]([3, 1, 1]))
    subst.append(List[Int]([1, 0, 1]))
    subst.append(List[Int]([2, 0, 1]))
    subst.append(List[Int]([4, 1, 1]))
    var fam = shape_family(List[Int]([Z, Y]), List[Int]([Y, Z]), subst)
    for base in range(2):
        var ns = List[Int]([1, 2]) if base == 0 else List[Int]([2, 1])
        var point = _line_family_at(ns)
        var paths = enumerate_point_paths(point, O, Y, 3, 6, Y, Z, 50, 20000)
        assert_true(len(paths) >= 1)
        var solved = 0
        for k in range(len(paths)):
            assert_true(verify_witness_line(point, O, Y, paths[k]))
            var lr = solve_lift(fam, point, ns, O, Y, paths[k])
            if not lr.ok:
                continue
            solved += 1
            for i in range(3):
                assert_true(poly_vanishes_under(lr.gamma[i], Prover()))
            assert_true(verify_witness_poly(fam, O, Y, lr.steps, Prover(lr.ineqs.copy())))
            for x in range(6):
                for y in range(6):
                    var at = List[Int]([x, y])
                    var inside = True
                    for f in range(len(lr.ineqs)):
                        if aff_eval(lr.ineqs[f], at) < 0:
                            inside = False
                    if inside:
                        assert_true(verify_witness_line(_line_family_at(at), O, Y, steps_at(lr.steps, at)))
        assert_true(solved >= 1)


def _tail_bilinear(forms: List[List[Int]], i: Int, j: Int) raises -> Poly:
    """`A + B e` over (n_0, n_1, e): forms i and j as A and B."""
    var tail = poly_from_aff(List[Int]([0, 0, 0, 1]))
    return poly_add(poly_from_aff(forms[i]), poly_mul(poly_from_aff(forms[j]), tail))


def test_product_lift_round_trip() raises:
    """Over (a, b, e) with tail e: for P = A + B e with A, B affine (all 135 forms with constant in -2..2 and coefficients in -1..1 as
    A, each paired with a B), the lifted affine form at (n, q(n)) equals P at n on [0, 4]^3, the
    lift has exactly the products that occur, and the zy|yz quantities
    2a - 2b + ae and f(-1) = ae + a - 2b + 2 lift to (0, 2, -2, 0, 1) and
    (2, 1, -2, 0, 1) over (n, q_a)."""
    var forms = _forms(-2, 2, 1, 3)
    var checked = 0
    for i in range(len(forms)):
        var j = (5 * i + 7) % len(forms)
        var p = _tail_bilinear(forms, i, j)
        var lift = product_lift_of(List[Poly]([p.copy()]), 3, 2)
        var want = List[Int]()
        for k in range(3):
            if forms[j][k + 1] != 0:
                want.append(k)
        assert_equal(len(lift.prods), len(want))
        for k in range(len(want)):
            assert_equal(lift.prods[k], want[k])
        var f = lift_affine(lift, p)
        for x in range(5):
            for y in range(5):
                for z in range(5):
                    var ns = List[Int]([x, y, z])
                    assert_equal(aff_eval(f, lift_point(lift, ns)), poly_eval(p, ns))
                    assert_equal(aff_eval(lift_form(lift, forms[i]), lift_point(lift, ns)), aff_eval(forms[i], ns))
        checked += 1
    assert_equal(checked, 135)
    var ae = poly_mul(poly_from_aff(List[Int]([0, 1, 0, 0])), poly_from_aff(List[Int]([0, 0, 0, 1])))
    var md = poly_add(poly_from_aff(List[Int]([0, 2, -2, 0])), ae)
    var f1 = poly_add(poly_from_aff(List[Int]([2, 1, -2, 0])), ae)
    var lift = product_lift_of(List[Poly]([md.copy(), f1.copy()]), 3, 2)
    assert_equal(len(lift.prods), 1)
    assert_equal(lift.slot(0), 4)
    assert_true(lift_affine(lift, md) == List[Int]([0, 2, -2, 0, 1]))
    assert_true(lift_affine(lift, f1) == List[Int]([2, 1, -2, 0, 1]))


def test_mccormick_envelope_holds_at_real_points() raises:
    """With every product of (a, b, e) lifted (e^2 included), for lower
    bounds in 0..2 per variable, every McCormick form is >= 0 at the real
    point over each n in [lo, lo + 4]^3, and is 0 where n_j = lo_j or e = lo_e."""
    var full = List[Poly]()
    for j in range(3):
        var unit = List[Int](length=4, fill=0)
        unit[j + 1] = 1
        full.append(poly_mul(poly_from_aff(List[Int]([0, 0, 0, 1])), poly_from_aff(unit)))
    var lift = product_lift_of(full, 3, 2)
    assert_equal(len(lift.prods), 3)
    for code in range(27):
        var lo = List[Int]([code % 3, (code // 3) % 3, code // 9])
        var env = mccormick_forms(lift, lo)
        assert_equal(len(env), 3)
        for x in range(lo[0], lo[0] + 5):
            for y in range(lo[1], lo[1] + 5):
                for z in range(lo[2], lo[2] + 5):
                    var ns = List[Int]([x, y, z])
                    var pt = lift_point(lift, ns)
                    for k in range(3):
                        var v = aff_eval(env[k], pt)
                        assert_true(v >= 0)
                        assert_equal(v, (ns[k] - lo[k]) * (z - lo[2]))


def _lift_raises(p: Poly, m: Int, e: Int) -> Bool:
    try:
        _ = product_lift_of(List[Poly]([p.copy()]), m, e)
    except:
        return True
    return False


def test_product_lift_fails_closed() raises:
    """With tail e = n_2 of three variables, n_0 n_1, n_0^2, n_0 n_1 n_2,
    e^3 and a variable n_3 raise, a tail outside the variables raises, and
    lift_affine raises on a product its lift does not carry."""
    var n0 = poly_from_aff(List[Int]([0, 1, 0, 0]))
    var n1 = poly_from_aff(List[Int]([0, 0, 1, 0]))
    var e = poly_from_aff(List[Int]([0, 0, 0, 1]))
    assert_false(_lift_raises(poly_add(poly_mul(n0, e), poly_mul(e, e)), 3, 2))
    assert_true(_lift_raises(poly_mul(n0, n1), 3, 2))
    assert_true(_lift_raises(poly_mul(n0, n0), 3, 2))
    assert_true(_lift_raises(poly_mul(poly_mul(n0, n1), e), 3, 2))
    assert_true(_lift_raises(poly_mul(poly_mul(e, e), e), 3, 2))
    var n3 = Poly()
    n3.add_term(mono_var(3), 1)
    assert_true(_lift_raises(n3, 3, 2))
    assert_true(_lift_raises(poly_const(1), 3, 3))
    var lift = product_lift_of(List[Poly]([poly_mul(n0, e)]), 3, 2)
    var raised = False
    try:
        _ = lift_affine(lift, poly_add(poly_mul(n1, e), poly_scale(n0, 2)))
    except:
        raised = True
    assert_true(raised)


def main() raises:
    test_polynomial_arithmetic_matches_evaluation()
    print("[PASS] test_polynomial_arithmetic_matches_evaluation")
    test_polynomial_prover_is_sound()
    print("[PASS] test_polynomial_prover_is_sound")
    test_polynomial_mode_agrees_with_line_mode()
    print("[PASS] test_polynomial_mode_agrees_with_line_mode")
    test_linear_lift_solves_point_paths()
    print("[PASS] test_linear_lift_solves_point_paths")
    test_product_lift_round_trip()
    print("[PASS] test_product_lift_round_trip")
    test_mccormick_envelope_holds_at_real_points()
    print("[PASS] test_mccormick_envelope_holds_at_real_points")
    test_product_lift_fails_closed()
    print("[PASS] test_product_lift_fails_closed")
    require_contract("psc.poly_line, the polynomial line mode of Theorem K's tail cells: polynomial products and sums evaluate as the products of their affine factors on [0, 3]^3, poly_nonneg_under is sound under every pair of assumptions with coefficients in -1..1 on [0, 5]^2 for products U V + W and (U V + W) U, vanishing needs both signs, and verify_witness_poly agrees with verify_witness_line on the line-mode family (z^a y^b, y^(b+1) z^(a+1)) and on its single-offset perturbations, the path holding at every point of [0, 4]^2 once instantiated; the point-path enumeration returns only verified paths, and solve_lift solves some to a path with a zero end offset that verify_witness_poly accepts on its carved region and that holds at every point of [0, 5]^2 inside it; psc.product_lift makes A + B e affine over (n, q) with q_j = n_j e, agreeing with the polynomial at every real point of [0, 4]^3 and lifting the zy|yz quantities 2a - 2b + ae and f(-1) exactly, its McCormick forms equal (n_j - lo_j)(e - lo_e) >= 0 at every real point above each lower bound in 0..2, and any other degree-2 monomial, any degree 3, a variable past the lift or an absent product raises")
