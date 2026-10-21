"""Exact cover identities and fail-closed receipt assembly, no proof promotion."""
from std.testing import assert_true
from psc.class_d_assembly import verify_class_d_cover, verify_class_d_receipts
from mojo_smoke.claims import require_contract
from psc.overlap_seed_patch import OverlapState
from psc.perron_field3 import CubicElt


def main() raises:
    verify_class_d_cover()
    var unequal = OverlapState(0,1,CubicElt())
    var equal = OverlapState(0,0,CubicElt())
    assert_true(unequal.shift.is_zero() and not unequal.is_coincidence())
    assert_true(equal.is_coincidence())
    # Empty, partial and duplicated receipts must never assemble a result.
    var plus = "CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6 boundary_lines= 73 finite_prefix_pip= 952 max_symbolic_vertices= 164\n"
    var minus = "MINUS_B0_COMPONENT_CERTIFIED a>=0 145 781 4\nMINUS_STRIP_CERTIFIED 0 n=b-1 threshold 42 vertices 140 finite_pip 42 crosschecks 42 47\nMINUS_STRIP_CERTIFIED 1 n=b-1 threshold 72 vertices 137 finite_pip 72 crosschecks 72 77\nMINUS_BOUNDARY_STRIPS_CERTIFIED strips=2 a=0,1 b>=1\nMINUS_SEED_COVER_COUNTS 145 9 3 2 1287 12255 1218 9034 2003\nMINUS_SEED_COVER_CERTIFIED a>=2 b>=1 all_real_seed_descendants_in_carrier=true abs_sum<=1 parameter_cap=none\nMINUS_CORE_BH_CERTIFIED a>=2 b>=1 rank 4\nCLASS_D_MINUS_RESIDUAL_BH_CERTIFIED a>=0 b>=0 components=4 universal_139=open\n"
    verify_class_d_receipts(plus,minus)
    var bad_inputs = List[String]()
    bad_inputs.append("")
    bad_inputs.append("CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6")
    var doubled = plus.copy()
    doubled += plus
    bad_inputs.append(doubled^)
    for bad in bad_inputs:
        var refused = False
        try:
            verify_class_d_receipts(bad,minus)
        except:
            refused = True
        assert_true(refused)
    var refused = False
    try:
        verify_class_d_receipts(plus,"")
    except:
        refused = True
    assert_true(refused)
    require_contract("class-D assembly: exact polynomial inverse and unimodular residual/low-chamber cover identities; both complete native component receipts required; missing, partial and duplicated receipts refuse; offset-zero hitting only; full integration acceptance and universal Issue139 remain separate")
