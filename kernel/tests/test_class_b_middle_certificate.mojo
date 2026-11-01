"""Uniform middle-regime certificates, exact g=12 exception, invalid candidates."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_b_middle_geometry import check_b_identity, certify_middle_members, certify_middle_core, certify_middle_closure, certify_middle_descent
from psc.class_b_ray_line import BRay
from psc.class_b_ray_certificate import certify_ray_rows
from psc.class_b_middle_tables import middle_rows
from psc.class_b_middle_potential_tables import middle_potentials


def main() raises:
    for eps in [-1, 1]:
        check_b_identity(eps)
        assert_equal(certify_middle_members(eps), 529)
        assert_equal(certify_middle_core(eps), 1851 if eps == -1 else 1875)
        assert_equal(certify_middle_closure(eps), 16604 if eps == -1 else 16098)
        var st = certify_middle_descent(eps, 4, False, 13 if eps == -1 else 16)
        assert_equal(st[10], 1153 if eps == -1 else 1141)
        assert_equal(st[11], 9)
        assert_equal(st[12], 1456 if eps == -1 else 1468)
        assert_equal(st[14], 3)
        var refused = False
        try:
            _ = certify_middle_core(eps, 4, True)
        except:
            refused = True
        assert_true(refused)
        refused = False
        try:
            _ = certify_middle_descent(eps, 4, True, 13 if eps == -1 else 16)
        except:
            refused = True
        assert_true(refused)
    var refused = False
    try:
        _ = certify_middle_descent(-1)  # common occurrence fails at g=12
    except:
        refused = True
    assert_true(refused)
    # This is the only middle residue at minus g=12; the existing exact
    # one-ray machinery supplies its piecewise occurrence instead.
    var st = certify_ray_rows(BRay(-1, 12, 6), 54, middle_rows(-1), middle_potentials(-1))
    assert_equal(st[0], 529)
    assert_equal(st[11], 9)
    require_contract("class-B middle regimes uniformly in unbounded g and l>=4: plus g>=16 with 2<=r<=g-14, minus g>=12 with 6<=r<=g-6; exact strict 529-row carriers contain strict core and swap seeds and are forward closed; X=abs(k)+b, 0<=b<=3, has a realizable decreasing child until offset zero; minus g=12 r=6 uses exact ray exception; removed carrier row and zero potential refuse; low/high residues and l<4, universal BH, G1 and PSC remain open")
