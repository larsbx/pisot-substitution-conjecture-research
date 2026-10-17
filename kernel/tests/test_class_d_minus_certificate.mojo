"""Parametric cover/rank checker and overstrong-proposal countercontrols."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_d_minus_certificate import certify_minus_tail, verify_minus_spine
from psc.class_d_minus_spine_data import minus_spine_rows
from psc.boundary_hitting_spine import minus_common_spine


def refused(rows: List[List[Int]]) -> Bool:
    try:
        _ = verify_minus_spine(rows)
    except:
        return True
    return False


def main() raises:
    assert_equal(certify_minus_tail(),List[Int]([145,6,9,18779,4]))
    assert_equal(minus_common_spine(3),List[Int]([145,779,6,4]))
    var rows = minus_spine_rows()
    var witness = -1
    for i in range(len(rows)):
        if rows[i][5] > 0:
            witness = i
            break
    assert_true(witness >= 0)
    rows[witness][5] = 0
    assert_true(refused(rows))
    rows = minus_spine_rows()
    rows[witness][6] = witness
    assert_true(refused(rows))
    rows = minus_spine_rows()
    rows[witness][8] += 1
    assert_true(refused(rows))
    rows = minus_spine_rows()
    rows[witness][7] = -1
    rows[witness][8] = 9
    assert_true(refused(rows))
    var empty = List[List[Int]]()
    assert_true(refused(empty))
    rows = minus_spine_rows()
    rows.append(rows[0].copy())
    assert_true(refused(rows))
    require_contract("minus class-D b=0 parametric certificate: all a>=2 covered by 145 interior labels; nine seed occurrences; complete segment-pair child closure; exact affine occurrence rank descent to offset zero; rejects false targets, non-strict ranks, wrong indices, eventually negative indices, empty and duplicate covers; whole-line base cases are checked by the driver")
