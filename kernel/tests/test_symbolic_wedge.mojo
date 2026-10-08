"""Exact regressions for the two-parameter overlap graph (psc.param_poly,
psc.symbolic_line on a wedge) and the class B wedge certificate
(symbolic_wedge_certificate).

docs/p1c-symbolic-wedge-2026-10-08.md. The quadrant sign reader is checked on
polynomials with known signs, including one that needs a Polya multiplier and
one whose sign changes inside every quadrant; the Rouche PIP step and the
bracketed signs at beta against concrete parameter points; one cone against its
pin; and the wedge cover, point by point.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from mojo_smoke.claims import require_contract
from psc.param_poly import P2, p2_affine, p2_at, p2_mul, p2_sub, p2_const, quadrant_sign
from psc.symbolic_line import (
    Eventual,
    LineField,
    certify_line,
    qx_affine,
    qx_const,
    tp_at_q,
    tp_coeff,
    tp_const,
    tp_neg,
    tp_scale,
    tp_sub,
    tp_t,
)
from symbolic_line_certificate import family_line, family_pqr, slope_family
from symbolic_wedge_certificate import (
    boundary_pins,
    certify_cone,
    check_cone_pin,
    cone_family,
    cone_pin,
    mode_of,
    pinned_boundary,
    wedge_pins,
)


def test_quadrant_signs() raises:
    var s = p2_affine(0, 1, 0)
    var d = p2_affine(0, 0, 1)
    # s d - 4 on s, d > 2: (2 + u)(2 + v) - 4 = 2u + 2v + uv
    var sd4 = p2_sub(p2_mul(s, d), p2_const(4))
    assert_equal(quadrant_sign(sd4, q_int(2), q_int(2), 0), 1)
    assert_equal(quadrant_sign(p2_sub(p2_const(0), sd4), q_int(2), q_int(2), 0), -1)
    # s - d changes sign in every quadrant
    assert_equal(quadrant_sign(p2_sub(s, d), q_int(5), q_int(5), 4), 0)
    # s^2 - s d + d^2 + 1 + s + d: one Polya multiplier clears the -s d
    var mixed = p2_sub(p2_mul(s, s), p2_mul(s, d))
    mixed = p2_sub(mixed, p2_sub(p2_const(0), p2_mul(d, d)))
    mixed = p2_sub(mixed, p2_affine(-1, -1, -1))
    assert_equal(quadrant_sign(mixed, Q.zero(), Q.zero(), 0), 0)
    assert_equal(quadrant_sign(mixed, Q.zero(), Q.zero(), 1), 1)


def test_the_eventual_region_grows_to_a_certificate() raises:
    """`s d - 30` needs a larger quadrant; the region found makes it positive at
    its corner, and a later read never shrinks it back."""
    var ev = Eventual()
    var p = p2_sub(p2_mul(p2_affine(0, 1, 0), p2_affine(0, 0, 1)), p2_const(30))
    assert_equal(ev.sign(p), 1)
    assert_true(Q.zero().le(p2_at(p, ev.threshold, ev.d_threshold)))
    var s0 = ev.threshold.copy()
    assert_equal(ev.sign(p2_affine(-1, 0, 1)), 1)
    assert_true(s0.le(ev.threshold))
    var refused = False
    try:
        _ = ev.sign(p2_affine(0, 1, -1))
    except:
        refused = True
    assert_true(refused)


def test_rouche_and_brackets_on_a_cone() raises:
    """Cone A of branch +1 is PIP by Rouche on its quadrant, and signs read
    from the bracket of beta agree with the Sturm count at a concrete point."""
    var line = family_line(cone_family(1, 0))
    assert_true(line.wedge)
    var ev = Eventual()
    var cert = certify_line(line, ev)
    assert_true(cert.holds)
    assert_true(len(line.field.brackets) > 0)
    var trace = tp_neg(tp_const(tp_coeff(line.field.chi, 2)))
    var below = tp_sub(tp_t(), trace)  # beta < trace
    var above = tp_sub(below, tp_const(qx_const(-1)))  # beta > trace - 1
    var gap = tp_scale(tp_sub(tp_scale(line.ell[2], qx_const(2)), line.ell[0]), qx_const(cert.ell_sign))
    var e = ev.first_integer_above() + 7
    var d = ev.first_integer_above_d() + 11
    var at = LineField(tp_at_q(line.field.chi, e, d))
    var ev_at = Eventual()
    var queries = [below.copy(), above.copy(), gap.copy()]
    for i in range(3):
        var symbolic = line.field.sign_at_beta(queries[i], ev)
        assert_true(symbolic != 0)
        assert_equal(at.sign_at_beta(tp_at_q(queries[i], e, d), ev_at), symbolic)
    assert_equal(line.field.sign_at_beta(below, ev), -1)
    assert_equal(line.field.sign_at_beta(above, ev), 1)


def test_a_cone_reproduces_its_pin() raises:
    var v = certify_cone(1, 1)
    assert_equal(v.symbolic_vertices, 74)
    check_cone_pin(v, cone_pin(1, 1))
    var off = v.copy()
    off.d0 += 1
    var refused = False
    try:
        check_cone_pin(off, cone_pin(1, 1))
    except:
        refused = True
    assert_true(refused)


def _on_family(f: List[Int], p: Int, q: Int, branch: Int, two: Bool, s0: Int, d0: Int) -> Bool:
    """Some parameter point of `f` (`t >= 0`; on a cone `t >= s0, d >= d0`) is `(p, q)`."""
    if f[6] != branch:
        return False
    var tmax = p + q + 2
    for t in range(tmax):
        for d in range(tmax if two else 1):
            if two and (t < s0 or d < d0):
                continue
            var pqr = family_pqr(f, t, d)
            if pqr[0] == p and pqr[1] == q:
                return True
    return False


def test_the_cones_and_the_boundary_lines_cover_the_wedge() raises:
    """Every (p, q) with q < p < 2q and q <= 40 lies in a pinned cone quadrant
    or on a pinned boundary line, for both branches."""
    for bi in range(2):
        var branch = 1 if bi == 0 else -1
        var lines = pinned_boundary(branch)
        var a = cone_pin(branch, 0)
        var b = cone_pin(branch, 1)
        for q in range(1, 41):
            for p in range(q + 1, 2 * q):
                var hit = _on_family(cone_family(branch, 0), p, q, branch, True, a[2], a[3])
                hit = hit or _on_family(cone_family(branch, 1), p, q, branch, True, b[2], b[3])
                for i in range(len(lines)):
                    if hit:
                        break
                    hit = _on_family(lines[i], p, q, branch, False, 0, 0)
                assert_true(hit)


def test_every_boundary_line_has_a_pin() raises:
    var pins = boundary_pins()
    var total = 0
    for bi in range(2):
        var lines = pinned_boundary(1 if bi == 0 else -1)
        total += len(lines)
        for i in range(len(lines)):
            var found = False
            for k in range(len(pins)):
                var same = True
                for j in range(7):
                    if pins[k][j] != lines[i][j]:
                        same = False
                if same:
                    found = True
            assert_true(found)
    assert_equal(len(pins), total)
    assert_equal(len(wedge_pins()), 4)
    for k in range(len(pins)):
        assert_equal(len(pins[k]), 12)


def assert_mode_refused(args: List[String]) raises:
    var refused = False
    try:
        _ = mode_of(args)
    except:
        refused = True
    assert_true(refused)


def test_the_command_line_is_strict() raises:
    assert_equal(mode_of(["cone", "1", "0"]), "cone")
    assert_equal(mode_of(["boundary", "-1", "2", "4"]), "boundary")
    assert_equal(mode_of(["wedge", "1"]), "wedge")
    assert_mode_refused(List[String]())
    assert_mode_refused(["cone", "1"])
    assert_mode_refused(["boundary", "1", "4", "4"])
    assert_mode_refused(["wedge", "x"])
    assert_mode_refused(["lines"])


def main() raises:
    test_quadrant_signs()
    print("[PASS] test_quadrant_signs")
    test_the_eventual_region_grows_to_a_certificate()
    print("[PASS] test_the_eventual_region_grows_to_a_certificate")
    test_rouche_and_brackets_on_a_cone()
    print("[PASS] test_rouche_and_brackets_on_a_cone")
    test_a_cone_reproduces_its_pin()
    print("[PASS] test_a_cone_reproduces_its_pin")
    test_the_cones_and_the_boundary_lines_cover_the_wedge()
    print("[PASS] test_the_cones_and_the_boundary_lines_cover_the_wedge")
    test_every_boundary_line_has_a_pin()
    print("[PASS] test_every_boundary_line_has_a_pin")
    test_the_command_line_is_strict()
    print("[PASS] test_the_command_line_is_strict")
    require_contract("Class B wedge certificate (docs/p1c-symbolic-wedge-2026-10-08.md): polynomials in (s, d) get a sign on an open quadrant only from a Polya certificate (s d - 4 on (2, 2); s - d refused; a mixed form needing one multiplier), and the quadrant only grows; a two-parameter cone is PIP by Rouche, and signs read from the bracket of beta agree with the Sturm count at a concrete point; cone B of branch +1 reproduces its pinned verdict (74 vertices, all hitting) and a verdict off its pin is refused; the pinned cone quadrants and boundary lines cover every (p, q) with q < p < 2q, q <= 40, on both branches, and every boundary line has a pinned verdict; the command line is strict")
