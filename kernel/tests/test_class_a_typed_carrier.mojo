"""Typed semilinear carrier: exact finite equivalence and refusal controls."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_a_typed_carrier import (
    template_rows, contains, certify_finite, certify_finite_rows,
)


def main() raises:
    assert_equal(len(template_rows()),89)
    assert_true(contains(4,1,2,4,-4,0))  # A_4
    assert_true(contains(4,2,0,0,-1,1))  # B_0
    assert_true(not contains(4,0,1,-5,8,-2))  # formal rectangle escape
    assert_true(not contains(4,0,2,-4,7,-1))
    assert_equal(certify_finite(4),List[Int]([275,275,5]))
    assert_equal(certify_finite(8),List[Int]([435,435,8]))
    assert_equal(certify_finite(18),List[Int]([835,835,15]))
    # A missing interval must be rejected, not counted as a complete cover.
    var original=template_rows()
    var damaged=List[List[Int]]()
    for i in range(len(original)-1):
        damaged.append(original[i].copy())
    var refused=False
    try:
        _=certify_finite_rows(4,damaged)
    except:
        refused=True
    assert_true(refused)
    for invalid in [3,49]:
        refused=False
        try:
            _=certify_finite(invalid)
        except:
            refused=True
        assert_true(refused)
    require_contract("class-A typed carrier finite-only: 89 affine interval rows, exact n=4/8/18 candidate-graph label equality, full ordered-child closure and finite offset-zero paths, removed-row/budget refusals; no uniform seed cover or #139 promotion")
