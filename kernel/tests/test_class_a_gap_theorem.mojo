"""Class-A gaps d>=5: residue coverage, the assembled theorem for both signs, and refusals."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_claim, require_contract
from psc.class_a_gap_theorem import certify_gap_theorem, eventual_cover, residue_cover, FIRST_GAP
from psc.class_a_gap_regime_tables import fitted_regimes, regime_floors


def raises_cover(eps: Int) -> Bool:
    try:
        _ = eventual_cover(eps)
    except:
        return True
    return False


def raises_theorem(eps: Int, l0: Int) -> Bool:
    try:
        _ = certify_gap_theorem(eps, l0)
    except:
        return True
    return False


def main() raises:
    # The fitted regimes tile every residue from the largest fitted floor on: minus from
    # d = 7 (middle 3 <= r <= d-4 meets low 0..2 and high d-3..d-1), plus from d = 11.
    assert_equal(eventual_cover(-1), 7)
    assert_equal(eventual_cover(1), 11)
    assert_true(raises_cover(0))
    # Below those gaps every residue is still covered: minus by regimes alone, plus by
    # regimes and the seven exceptional ray tables (5,1), (5,2), (6,1), (6,2), (7,2), (7,3), (8,3).
    for d in range(FIRST_GAP, 13):
        for c in residue_cover(-1, d):
            assert_true(c >= 0)
    var exceptional = 0
    for d in range(FIRST_GAP, 13):
        for c in residue_cover(1, d):
            if c < 0:
                exceptional += 1
    assert_equal(exceptional, 7)
    assert_true(residue_cover(1, 5)[1] < 0 and residue_cover(1, 5)[2] < 0 and residue_cover(1, 5)[0] >= 0)
    # Every fitted regime has a registered uniform floor at or above its fitted floor.
    var floors = regime_floors()
    for spec in fitted_regimes():
        var seen = False
        for f in floors:
            if f[0] == spec[0] and f[1] == spec[1] and f[2] == spec[2]:
                assert_true(f[3] >= spec[4])
                seen = True
        assert_true(seen)
    # The assembled theorem, both signs, l >= 5: regimes from their uniform floors, finite
    # rays on regime tables where the uniform floor exceeds the fitted one, exceptional rays
    # on their own tables, exact complete graphs below the ray floors.
    var minus = certify_gap_theorem(-1, 5)
    assert_equal(minus[0], 7)
    assert_equal(minus[2], 0)
    var plus = certify_gap_theorem(1, 5)
    assert_equal(plus[0], 11)
    assert_equal(plus[2], 7)
    # Refusals: a third sign, a non-positive l floor.
    assert_true(raises_theorem(0, 5))
    assert_true(raises_theorem(1, 0))
    require_contract("class-A gaps d>=5, both signs, every n = d l + r with l>=5: the fitted residue regimes tile every residue from d=7 (minus) and d=11 (plus) on, each regime certifies closure and descent uniformly from its registered gap floor, the finite gaps below it are ray certificates on the same tables with exact complete graphs below the ray floor, the seven plus residues no regime reaches are ray certificates on their own tables, and the assembly refuses a third sign, a non-positive floor and an uncovered residue")
    require_claim("ClassABoundaryHittingHighGaps")
