"""Regressions for checked rational interval arithmetic and Perron enclosures."""

from std.testing import assert_equal, assert_false, assert_true
from psc.bpa import substitution_incidence
from psc.mat3 import Mat3
from psc.overlap_interval_audit import audit_seed_overlap_interval_margins
from psc.perron_field3 import CubicElt, build_perron_field3
from psc.perron_interval import (
    cubic_perron_interval,
    interval_sign_at_perron,
    perron_root_interval,
    perron_sign_decision,
)
from psc.rational_interval import (
    CheckedRat,
    RatInterval,
    eval_int_poly_at_rat,
    integer_interval,
    interval_horner_int,
)


def determinant_two_sigma() -> List[List[Int]]:
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    var sigma = List[List[Int]]()
    sigma.append(a0^)
    sigma.append(a1^)
    sigma.append(a2^)
    return sigma^


def test_checked_rational_normalization_and_order() raises:
    assert_true(CheckedRat(2, 4) == CheckedRat(1, 2))
    assert_true(CheckedRat(1, -2) == CheckedRat(-1, 2))
    assert_equal(CheckedRat(2, 3).compare(CheckedRat(3, 4)), -1)
    assert_true(CheckedRat(1, 3).add(CheckedRat(1, 6)) == CheckedRat(1, 2))
    assert_true(CheckedRat(2, 3).mul(CheckedRat(9, 4)) == CheckedRat(3, 2))


def test_natural_interval_extension_contains_point_values() raises:
    # p(x)=x^2-2 on x in [1,2] has natural extension [-1,2].
    var x = integer_interval(1, 2)
    var coeffs: List[Int] = [-2, 0, 1]
    var box = interval_horner_int(coeffs, x)
    assert_true(box.lo == CheckedRat(-1, 1))
    assert_true(box.hi == CheckedRat(2, 1))
    assert_true(box.contains_zero())
    assert_equal(box.strict_sign(), 0)

    var positive_coeffs: List[Int] = [1, 1]
    var positive = interval_horner_int(positive_coeffs, x)
    assert_equal(positive.strict_sign(), 1)


def test_interval_division_across_zero_fails_closed() raises:
    var numerator = integer_interval(1, 2)
    var denominator = RatInterval(CheckedRat(-1, 1), CheckedRat(1, 1))
    var caught = False
    try:
        _ = numerator.div(denominator)
    except:
        caught = True
    assert_true(caught)


def test_checked_interval_overflow_fails_closed() raises:
    var caught = False
    try:
        _ = CheckedRat(Int.MAX, 1).add(CheckedRat(1, 1))
    except:
        caught = True
    assert_true(caught)


def test_perron_root_has_exact_rational_bracket() raises:
    var sigma = determinant_two_sigma()
    var field = build_perron_field3(Mat3(substitution_incidence(sigma)))
    var box = perron_root_interval(field, 10)
    assert_true(box.lo.compare(CheckedRat(2, 1)) > 0)
    assert_true(box.hi.compare(CheckedRat(3, 1)) < 0)

    var chi: List[Int] = [field.chi0, field.chi1, field.chi2, 1]
    var flo = eval_int_poly_at_rat(chi, box.lo).sign()
    var fhi = eval_int_poly_at_rat(chi, box.hi).sign()
    assert_true(flo != 0)
    assert_true(fhi != 0)
    assert_true(flo != fhi)


def test_symbolic_zero_is_not_a_strict_interval_certificate() raises:
    var sigma = determinant_two_sigma()
    var field = build_perron_field3(Mat3(substitution_incidence(sigma)))
    var zero = perron_sign_decision(field, CubicElt(), 6)
    assert_equal(zero.sign, 0)
    assert_false(zero.interval_certified)


def test_interval_first_perron_sign_certifies_easy_and_falls_back_near_root() raises:
    var sigma = determinant_two_sigma()
    var field = build_perron_field3(Mat3(substitution_incidence(sigma)))

    # beta-1 is separated from zero by even a coarse rational enclosure.
    assert_equal(interval_sign_at_perron(field, CubicElt(-1, 1, 0), 6), 1)
    var easy = perron_sign_decision(field, CubicElt(-1, 1, 0), 6)
    assert_equal(easy.sign, 1)
    assert_true(easy.interval_certified)

    # This Codex counter-calibration lies extremely close to the Perron root.
    # A modest interval box must remain honest and say "unknown"; the exact
    # Sturm--Tarski fallback then supplies the negative sign.
    var near = CubicElt(-152138, 67035, 0)
    assert_equal(interval_sign_at_perron(field, near, 10), 0)
    var decided = perron_sign_decision(field, near, 10)
    assert_equal(decided.sign, -1)
    assert_false(decided.interval_certified)

    var enclosure = cubic_perron_interval(field, near, 10)
    assert_true(enclosure.contains_zero())


def test_canonical_overlap_margin_interval_calibration() raises:
    # This is a calibration pass, not yet a pinned interval-count theorem.
    # The graph size is already canonical from the seed-patch regression; here
    # we audit how much of its strict geometry one fixed rational beta box
    # certifies before the algebraic fallback is needed.
    var audit = audit_seed_overlap_interval_margins(
        determinant_two_sigma(), 10, 20000
    )
    assert_equal(audit.state_count, 628)
    assert_equal(audit.margin_count, 1256)
    assert_equal(
        audit.interval_certified_count + audit.fallback_count,
        audit.margin_count,
    )
    assert_true(audit.interval_certified_count > 0)
    print("canonical overlap margins:", audit.margin_count)
    print("interval-certified margins:", audit.interval_certified_count)
    print("algebraic-fallback margins:", audit.fallback_count)
    if audit.has_uniform_interval_lower_margin:
        print(
            "minimum certified rational overlap margin:",
            audit.minimum_interval_lower_margin,
        )


def main() raises:
    test_checked_rational_normalization_and_order()
    print("[PASS] test_checked_rational_normalization_and_order")
    test_natural_interval_extension_contains_point_values()
    print("[PASS] test_natural_interval_extension_contains_point_values")
    test_interval_division_across_zero_fails_closed()
    print("[PASS] test_interval_division_across_zero_fails_closed")
    test_checked_interval_overflow_fails_closed()
    print("[PASS] test_checked_interval_overflow_fails_closed")
    test_perron_root_has_exact_rational_bracket()
    print("[PASS] test_perron_root_has_exact_rational_bracket")
    test_symbolic_zero_is_not_a_strict_interval_certificate()
    print("[PASS] test_symbolic_zero_is_not_a_strict_interval_certificate")
    test_interval_first_perron_sign_certifies_easy_and_falls_back_near_root()
    print("[PASS] test_interval_first_perron_sign_certifies_easy_and_falls_back_near_root")
    test_canonical_overlap_margin_interval_calibration()
    print("[PASS] test_canonical_overlap_margin_interval_calibration")
    print("8 rational-interval Mojo tests passed.")
