"""Higher-sum formal cycles require a seed-reachability firewall."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract, require_claim
from psc.class_d_minus_high_sum_cycles import verify_high_sum_ray, high_sum_seed_sample
from psc.class_d_minus_cycle_superset import CycleState
from psc.class_d_minus_recurrent_support import classify
from psc.class_d_minus_spine_data import minus_spine_rows


def main() raises:
    verify_high_sum_ray()
    for k in [2,3,8]:
        var report = high_sum_seed_sample(k)
        assert_equal(report[1],0)  # finite observation only
        # Never whitelist these formal high-sum cycles in the seed diagnostic.
        assert_equal(classify(CycleState(2,1,-2*k,4*k,-3*k),minus_spine_rows()),"unexplained")
    var refused = False
    try:
        _ = high_sum_seed_sample(2,1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = high_sum_seed_sample(Int.MAX)
    except:
        refused = True
    assert_true(refused)
    require_contract("minus class-D unbounded genuine formal two-cycles on a=2k-1,b=1,k>=2 have |sum|=k; three complete finite seed graphs omit these pairs; no universal seed-reachability verdict; caps refuse and high-sum seed labels remain unexplained")
    require_claim("MinusHighSumFormalCycleRay")
