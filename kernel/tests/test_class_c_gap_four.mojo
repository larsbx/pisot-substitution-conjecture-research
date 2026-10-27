"""Complete gap-four certificates on both C signs, domain and pin controls."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.pisot import CubicScreen
from class_c_gap_four import gap_four, check_verdict, certify_gap_four


def main() raises:
    var screen = CubicScreen()
    for eps in [1, -1]:
        var spec = gap_four(eps)
        var first = 3 if eps == 1 else 9
        assert_true(spec.admissible(first))
        assert_true(screen.is_pip(Mat3(substitution_incidence(spec.member(first)))))
        if eps == 1:
            assert_true(not spec.admissible(first - 1))
        else:
            assert_true(not screen.is_pip(Mat3(substitution_incidence(spec.member(first - 1)))))
        assert_equal(abs(Mat3(substitution_incidence(spec.member(first))).det()), 2)
        # The third image starts AND ends in c, unlike the class-A tables.
        var sigma = spec.member(first)
        assert_equal(sigma[2][0], 1)
        assert_equal(sigma[2][len(sigma[2]) - 1], 1)
        var v = certify_gap_four(eps)
        var refused = False
        try:
            check_verdict(-eps, v)
        except:
            refused = True
        assert_true(refused)
        v.symbolic_vertices += 1
        refused = False
        try:
            check_verdict(eps, v)
        except:
            refused = True
        assert_true(refused)
    var refused = False
    try:
        _ = gap_four(0)
    except:
        refused = True
    assert_true(refused)
    require_contract("class-C gap four: both complete symbolic tails, every admissible PIP finite-prefix member, two exact vertex-set cross-checks per sign; determinant, first/last labels, PIP-domain endpoint, invalid sign, opposite-sign and corrupted-verdict controls; d>=5 and universal #139 remain open")
