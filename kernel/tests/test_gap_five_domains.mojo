"""Exact PIP endpoints and invalid-sign control for the gap-five continuation."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.pisot import CubicScreen
from psc.symbolic_line import zero_descendants
from psc.class_a_line import ALine
from class_c_gap_five import gap_five


def main() raises:
    var screen = CubicScreen()
    for eps in [1, -1]:
        var spec = gap_five(eps)
        var first = 5 if eps == 1 else 11
        assert_true(spec.admissible(first))
        assert_true(spec.admissible(first - 1))
        var m = Mat3(substitution_incidence(spec.member(first)))
        assert_true(screen.is_pip(m))
        assert_equal(abs(m.det()), 2)
        assert_true(not screen.is_pip(Mat3(substitution_incidence(spec.member(first - 1)))))
        var sigma = spec.member(first)
        assert_equal(sigma[2][0], 1)
        assert_equal(sigma[2][len(sigma[2]) - 1], 1)
        var afirst = 0 if eps == 1 else 3
        var a = ALine(5, eps, afirst % 5)
        assert_true(screen.is_pip(Mat3(substitution_incidence(a.member(afirst)))))
        var refused = False
        try:
            ALine(5, eps, (afirst + 4) % 5).check_domain(afirst - 1)
        except:
            refused = True
        assert_true(refused)
    var refused = False
    try:
        _ = gap_five(0)
    except:
        refused = True
    assert_true(refused)
    # Removing a productive exit must expose a target-free recurrent component.
    var adj = List[List[Int]]()
    adj.append([1])
    adj.append([0])
    adj.append(List[Int]())
    var zero = List[Bool]([False, False, True])
    var good = zero_descendants(adj, zero)
    assert_true(not good[0] and not good[1] and good[2])
    adj[1].append(2)
    good = zero_descendants(adj, zero)
    assert_true(good[0] and good[1] and good[2])
    require_contract("gap-five A/C exact PIP endpoints, determinant and C occurrence labels; invalid sign and preceding A member refuse; target-free cycle needs a productive exit; no all-parameter A or universal hitting claim")
