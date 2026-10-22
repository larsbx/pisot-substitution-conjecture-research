"""Finite ordered-child first-hit descent and centered-row rank obstruction."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_d2_descent_probe import (
    finite_d2_descent,uniform_centered_slice_obstruction,
    uniform_centered_slice_replay,certify_d2_uniform_center_paths,
    replay_d2_center_paths,
)
from psc.class_a_d2_parity_carrier import inferred_template


def main() raises:
    uniform_centered_slice_replay()
    assert_equal(certify_d2_uniform_center_paths(),List[Int]([2,4,5]))
    for n in [4,7,8,9,12]:
        replay_d2_center_paths(n)
    assert_equal(finite_d2_descent(7),List[Int]([231,8,223,5,3]))
    assert_equal(finite_d2_descent(8),List[Int]([265,8,257,5,3]))
    assert_equal(finite_d2_descent(9),List[Int]([271,8,263,6,3]))
    assert_equal(finite_d2_descent(10),List[Int]([305,8,297,6,3]))
    assert_equal(finite_d2_descent(11),List[Int]([311,8,303,7,3]))
    assert_equal(finite_d2_descent(12),List[Int]([345,8,337,7,3]))
    for n in [3,25]:
        var refused=False
        try:
            _=finite_d2_descent(n)
        except:
            refused=True
        assert_true(refused)
    var broken=inferred_template(8,12)
    var nrows=List[List[Int]]()
    for row in broken:
        if row[0]==0 and row[1]==0 and row[2]==0 and row[3]==0:
            continue
        nrows.append(row.copy())
    var refused=False
    try:
        _=uniform_centered_slice_obstruction(nrows)
    except:
        refused=True
    assert_true(refused)
    require_contract("Class-A d2 uniform n>=4 explicit two-step centered x/x paths (0,2)->(1,2) and (2,0)->(2,1) with exact coefficient-checked strict real geometry; exact finite first-boundary-hit path witnesses at n=7..12, all actual decreasing adjacency and eight offset-zero targets, canonical centered x/x k=-1,0,1 depths 2,0,2; uniform proof that a target-normalized single affine rank on that three-point slice is impossible, requiring a piece split for that strategy; no all-n hitting promotion")
