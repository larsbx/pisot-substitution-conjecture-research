"""Exact regressions for the symbolic line overlap graph (psc.symbolic_line) and
the class B line certificate (symbolic_line_certificate).

docs/p1b-symbolic-line-2026-10-07.md. The parametric sign reader is checked
against the same query at concrete `q`, the pseudo-remainder against its
sign-preservation contract, the PIP certificate on a member and a non-member
line, and the certificate itself is pinned.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from mojo_smoke.claims import require_contract
from psc.symbolic_line import (
    Eventual,
    Line,
    LineField,
    certify_line,
    qx_affine,
    qx_const,
    tp_add,
    tp_at_q,
    tp_const,
    tp_prem,
    tp_scale,
    tp_sub,
    tp_t,
)
from a1_normal_form_census import CLASS_A, CLASS_B, CLASS_C, CLASS_D, class_member
from symbolic_line_certificate import (
    ClassLine,
    certify,
    PIN_FIELDS,
    certified_lines,
    check_pinned,
    class_b,
    class_b_line,
    certify_class_b_line,
    mode_of,
    pinned,
    spec_of,
)


def test_eventual_sign_records_the_largest_root() raises:
    var ev = Eventual()
    # (q - 10)(q - 3) = q^2 - 13 q + 30
    var s = ev.sign([q_int(30), q_int(-13), q_int(1)])
    assert_equal(s, 1)
    assert_true(q_int(10).le(ev.threshold))
    assert_equal(ev.sign(qx_const(-4)), -1)
    assert_equal(ev.sign(List[Q]()), 0)


def test_parametric_signs_agree_with_concrete_signs() raises:
    """Beta = q + 4 - 3/q + ...: below q + 4, above q + 3, for every large q;
    the same queries at q = 60 with constant coefficients agree."""
    var line = class_b_line()
    var ev = Eventual()
    var cert = certify_line(line, ev)
    assert_true(cert.holds)
    var below = tp_sub(tp_t(), tp_const(qx_affine(4, 1)))  # t - (q + 4)
    var above = tp_sub(tp_t(), tp_const(qx_affine(3, 1)))  # t - (q + 3)
    assert_equal(line.field.sign_at_beta(below, ev), -1)
    assert_equal(line.field.sign_at_beta(above, ev), 1)
    var at60 = LineField(tp_at_q(line.field.chi, 60))
    var ev60 = Eventual()
    assert_equal(at60.sign_at_beta(tp_at_q(below, 60), ev60), -1)
    assert_equal(at60.sign_at_beta(tp_at_q(above, 60), ev60), 1)
    # ell_x / ell_y -> 2 from below: 2 ell_y - ell_x > 0 with the tile lengths oriented positive
    var gap = tp_scale(tp_sub(tp_scale(line.ell[2], qx_const(2)), line.ell[0]), qx_const(cert.ell_sign))
    assert_equal(line.field.sign_at_beta(gap, ev), 1)
    assert_equal(at60.sign_at_beta(tp_at_q(gap, 60), ev60), 1)


def test_pseudo_remainder_keeps_the_sign_at_beta() raises:
    var line = class_b_line()
    var ev = Eventual()
    _ = certify_line(line, ev)
    var g = tp_add(tp_scale(tp_t(), qx_affine(-1, 2)), tp_const(qx_affine(5, -3)))
    var g3 = tp_add(g, tp_scale(line.field.chi, qx_const(7)))  # same value at beta
    var r = tp_prem(g3, line.field.chi)
    assert_equal(line.field.sign_at_beta(r, ev), line.field.sign_at_beta(g, ev))


def test_a_line_with_determinant_zero_is_not_certified() raises:
    """Runs q, q, q with endings (x, x, c, x): det M = 2 (r - q) = 0."""
    var line = Line([0, 1, 1], [0, 0, 0], [qx_affine(0, 1), qx_affine(0, 1), qx_affine(0, 1)], 2)
    var ev = Eventual()
    assert_false(certify_line(line, ev).holds)


def test_the_class_b_line_certificate() raises:
    var v = certify_class_b_line()
    assert_equal(v.q0, 52)
    assert_equal(v.symbolic_vertices, 119)
    assert_equal(v.finite_members, 52)
    assert_equal(v.finite_non_pip, 0)
    check_pinned(v, pinned(2, 2, 1))


def test_a_second_line_of_class_b_is_certified() raises:
    """Theorem L' (docs/p1-seed-strength-2026-10-08.md): the line p = q + 1,
    r = q + 1 is certified by the same method, with its own threshold."""
    var v = certify_class_b_line(1, 1, 1)
    assert_equal(v.q0, 14)
    assert_equal(v.symbolic_vertices, 121)
    assert_equal(v.finite_members, 14)
    assert_equal(v.finite_non_pip, 0)
    assert_equal(v.finite_outside, 0)
    check_pinned(v, pinned(1, 1, 1))
    # a verdict that differs from its pin is refused
    var off = v.copy()
    off.symbolic_vertices += 1
    var refused = False
    try:
        check_pinned(off, pinned(1, 1, 1))
    except:
        refused = True
    assert_true(refused)


def test_every_listed_line_has_a_pinned_verdict() raises:
    """Each row is a class, six affine coefficients and a five-field verdict,
    no line is listed twice, and every row names a valid line; the evidence
    workflow runs each one against its pin."""
    var lines = certified_lines()
    for i in range(len(lines)):
        assert_equal(len(lines[i]), PIN_FIELDS)
        var spec = spec_of(lines[i])
        assert_equal(len(pinned(spec)), PIN_FIELDS)
        for j in range(i):
            assert_false(spec.key() == spec_of(lines[j]).key())
    assert_equal(len(pinned(3, 0, 1)), 0)


def test_a_class_line_names_its_normal_form_members() raises:
    """ClassLine reads p, q, r off its coefficients, builds the normal-form
    member, and its symbolic images agree with that member's run lengths."""
    var spec = ClassLine(CLASS_D, [1, 1, 1, 0, 2, 0])  # p = n + 1, q = n, r = 2n
    var sigma = spec.member(5)
    assert_true(sigma == class_member(CLASS_D, 6, 5, 10))
    assert_true(spec.admissible(0))
    # classes A-C are admissible only where Lemma P1's p > q holds
    assert_false(ClassLine(CLASS_A, [1, 0, 1, 0, 1, 1]).admissible(3))
    assert_true(class_b(1, 1, 1).key() == List[Int]([CLASS_B, 1, 1, 1, 0, 1, 1]))
    var refused = False
    try:
        _ = ClassLine(4, [1, 0, 1, 0, 1, 0])
    except:
        refused = True
    assert_true(refused)


def test_a_class_d_line_is_certified() raises:
    """Theorem L'' (docs/p1b-boundary-hitting-progress-2026-10-08.md §4): the
    class D line p = n + 1, q = n, r = n + 3 is certified by the same method
    and reproduces its pin; class D has no Lemma P1 cut, so n = 3 counts as
    not PIP rather than outside."""
    var spec = ClassLine(CLASS_D, [1, 1, 1, 0, 1, 3])
    var v = certify(spec)
    assert_equal(v.q0, 18)
    assert_equal(v.symbolic_vertices, 97)
    assert_equal(v.finite_members, 17)
    assert_equal(v.finite_non_pip, 1)
    assert_equal(v.finite_outside, 0)
    check_pinned(v, pinned(spec))


def assert_mode_refused(args: List[String]) raises:
    var refused = False
    try:
        _ = mode_of(args)
    except:
        refused = True
    assert_true(refused)


def test_the_command_line_is_strict() raises:
    """No argument, three integers, or `lines`; anything else raises instead of
    silently certifying the default line."""
    assert_equal(mode_of(List[String]()), "default")
    assert_equal(mode_of(["lines"]), "lines")
    assert_equal(mode_of(["1", "2", "-1"]), "line")
    assert_mode_refused(["2", "2"])
    assert_mode_refused(["foo"])
    assert_mode_refused(["2", "x", "1"])
    assert_mode_refused(["1", "2", "3", "4"])
    assert_equal(mode_of(["D", "1", "1", "1", "0", "2", "0"]), "class")
    assert_mode_refused(["E", "1", "1", "1", "0", "2", "0"])
    assert_mode_refused(["D", "1", "1", "1", "0", "2", "x"])


def test_a_line_that_leaves_the_pisot_class_is_refused() raises:
    """p = 3 q + 1, r = q - 1 has a second eigenvalue outside the unit disc for
    large q: the certificate must refuse it at the PIP step."""
    var refused = False
    try:
        _ = certify_class_b_line(3, 1, -1)
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_eventual_sign_records_the_largest_root()
    print("[PASS] test_eventual_sign_records_the_largest_root")
    test_parametric_signs_agree_with_concrete_signs()
    print("[PASS] test_parametric_signs_agree_with_concrete_signs")
    test_pseudo_remainder_keeps_the_sign_at_beta()
    print("[PASS] test_pseudo_remainder_keeps_the_sign_at_beta")
    test_a_line_with_determinant_zero_is_not_certified()
    print("[PASS] test_a_line_with_determinant_zero_is_not_certified")
    test_the_class_b_line_certificate()
    print("[PASS] test_the_class_b_line_certificate")
    test_a_second_line_of_class_b_is_certified()
    print("[PASS] test_a_second_line_of_class_b_is_certified")
    test_a_line_that_leaves_the_pisot_class_is_refused()
    print("[PASS] test_a_line_that_leaves_the_pisot_class_is_refused")
    test_every_listed_line_has_a_pinned_verdict()
    print("[PASS] test_every_listed_line_has_a_pinned_verdict")
    test_the_command_line_is_strict()
    print("[PASS] test_the_command_line_is_strict")
    test_a_class_line_names_its_normal_form_members()
    print("[PASS] test_a_class_line_names_its_normal_form_members")
    test_a_class_d_line_is_certified()
    print("[PASS] test_a_class_d_line_is_certified")
    require_contract("Theorem L certificate (class B line sigma_q: x -> x y^(2q+2) x, c -> c y^q x, y -> c y^(q+1) x): the symbolic swap-seed overlap graph, decided by parametric Sturm-Tarski queries over Q[q] with certified threshold, has 119 vertices for every q >= 52, all with an offset-zero descendant, and the line is certified PIP there; every q in 0..51 is PIP and its exact seed-reachable graph (screened kernel) has every vertex hitting; at q = 52 and 57 the symbolic graph with q substituted equals the exact graph; parametric signs agree with concrete signs at q = 60; pseudo-remainders keep the sign at beta; a det-0 line is refused")
    require_contract("Theorem L' certificate: the class B line p = q + 1, r = q + 1 is certified (121 symbolic vertices for every q >= 14, all hitting; q < 14: 14 PIP members, all hitting); the line p = 3q + 1, r = q - 1, which leaves the Pisot class, is refused; certified_lines() pins every listed verdict and a verdict off its pin is refused; the command line accepts only no argument, SLOPE K BRANCH, CLASS AP BP AQ BQ AR BR or lines")
    require_contract("Theorem L'' driver: a ClassLine of Theorem E's class A, B, C or D builds its normal-form members, Lemma P1's p > q bounds the admissible cone in classes A-C, and every pinned row names a distinct valid line; the class D line p = n + 1, q = n, r = n + 3 is certified (97 symbolic vertices for every n >= 18, all hitting; n < 18: 17 PIP members, all hitting, 1 not PIP) and reproduces its pin")
