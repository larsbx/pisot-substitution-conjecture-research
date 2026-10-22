"""All-n d2 fixed corridor: real geometry, ordered child and mutation controls."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_d2_fixed_corridor_data import corridor_rows
from psc.class_a_d2_fixed_corridor import (
    certify_uniform_fixed_corridor,certify_corridor_rows,
    certify_uniform_candidate_inclusion,_positive_quadratic,
    _child_label,
)


def main() raises:
    assert_equal(certify_uniform_fixed_corridor(),List[Int]([80,8,72,4,160]))
    var records=corridor_rows()
    assert_equal(certify_uniform_candidate_inclusion(records.copy()),List[Int]([80,80]))
    _positive_quadratic(List[Int]([0,1,0]))  # h>0
    for bad_poly in [
        List[Int]([0,0,0]),
        List[Int]([-1,0,0]),
        List[Int]([0,-1,0]),
    ]:
        var rejected=False
        try:
            _positive_quadratic(bad_poly)
        except:
            rejected=True
        assert_true(rejected)
    # Tampered top proper-prefix index must be rejected, not interpreted
    # as a witness on a finite source parameter.
    var bad=records.copy()
    var first=bad[0].copy()
    first[6]=5
    bad[0]=first
    var rejected=False
    try:
        _=certify_corridor_rows(bad)
    except:
        rejected=True
    assert_true(rejected)
    # A changed chosen child or rank violates the strict descent.
    bad=records.copy()
    first=bad[0].copy()
    first[8]=0
    bad[0]=first
    rejected=False
    try:
        _=certify_corridor_rows(bad)
    except:
        rejected=True
    assert_true(rejected)
    # A duplicate label cannot slip through a cardinality-only check.
    bad=records.copy()
    bad[5]=records[0].copy()
    rejected=False
    try:
        _=certify_corridor_rows(bad)
    except:
        rejected=True
    assert_true(rejected)
    # Removing the sum-zero cancellation invalidates all-n child algebra.
    bad=records.copy()
    first=bad[0].copy()
    first[4]+=1
    bad[0]=first
    rejected=False
    try:
        _=certify_corridor_rows(bad)
    except:
        rejected=True
    assert_true(rejected)
    # Zero-rank targets must have precisely zero physical shift.
    bad=records.copy()
    var target=bad[3].copy()
    target[2]=1
    bad[3]=target
    rejected=False
    try:
        _=certify_corridor_rows(bad)
    except:
        rejected=True
    assert_true(rejected)
    require_contract("Class-A d2 true all-n>=4 fixed corridor of 80 explicit strict sum-zero states: 160 exact quadratic margins and 72 uniformly legal proper-prefix decreasing occurrences, 8 offset-zero targets, max hit 4; all 80 lie in both formal parity candidates on their rays, with malformed index, child, rank, duplicate, sum and strict-boundary refusals; does NOT prove full d2 carrier hitting")
