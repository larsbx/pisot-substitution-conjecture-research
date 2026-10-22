"""All-n class-A affine child-closure proof and strict negative controls."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_uniform_closure import (
    certify_uniform_forward_closure, certify_tail_rows,
    _gap_excluded, _nonnegative_on_small_h, Affine,
)
from psc.class_a_typed_carrier import template_rows


def main() raises:
    assert_equal(certify_uniform_forward_closure(),List[Int]([1528,1006,505,501]))
    assert_true(_nonnegative_on_small_h(List[Int]([0,0,0,0]))) # equality excludes strict interior
    assert_true(_nonnegative_on_small_h(List[Int]([0,1,0,0])))
    assert_true(not _nonnegative_on_small_h(List[Int]([0,-1,0,0])))
    # A narrowed target row omits an actual strict occurrence for n>=8;
    # the whole symbolic closure must refuse, not downgrade to finite evidence.
    var broken=template_rows()
    broken[0]=List[Int]([0,0,-1,-1,0,0,0,0])
    var refused=False
    try:
        _=certify_tail_rows(broken)
    except:
        refused=True
    assert_true(refused)
    # Strongest input failure is never silently skipped.
    var incomplete=List[List[Int]]()
    for i in range(88):
        incomplete.append(template_rows()[i].copy())
    refused=False
    try:
        _=certify_tail_rows(incomplete)
    except:
        refused=True
    assert_true(refused)
    require_contract("class-A all-n=4..infinity typed forward closure: 4 exact finite bases and 1528 stable affine case cells covering 1006 gap exclusions (505 left/501 right); integer coefficient and mutation refusals; no all-state hitting or universal PSC claim")
