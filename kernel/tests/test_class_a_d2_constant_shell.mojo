"""All-n 518-state d2 constant preimage shell, with explicit refusals."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_d2_constant_shell import (
    certify_uniform_constant_shell,certify_shell_rows,
    _prefix,_strict_margin,_actual_child,
)
from psc.class_a_d2_constant_shell_data import shell_rows
from psc.class_a_d2_fixed_corridor_data import corridor_rows


def main() raises:
    assert_equal(certify_uniform_constant_shell(),
                 List[Int]([518,80,518,1036,5,259,259]))
    var src=shell_rows()
    var core=corridor_rows()
    var prefix_low=_prefix(1,0,4)
    assert_equal(prefix_low[0],2)
    var prefix_high=_prefix(2,1,2)
    assert_equal(prefix_high[0],1)  # last c for y
    for invalid in [List[Int]([0,0,0]),
                    List[Int]([-1,0,0]),
                    List[Int]([0,-1,0])]:
        var refused=False
        try:
            _strict_margin(invalid)
        except:
            refused=True
        assert_true(refused)
    var refused=False
    try:
        _=_prefix(0,1,4) # x last is n+3; n+4 is invalid.
    except:
        refused=True
    assert_true(refused)
    # A chosen child does not admit an arbitrary malformed near-LAST index.
    var damaged=src.copy()
    var first=damaged[0].copy()
    first[7]=4
    damaged[0]=first
    refused=False
    try:
        _=certify_shell_rows(damaged,core)
    except:
        refused=True
    assert_true(refused)
    # The offset-sum cancellation is essential and cannot be skipped.
    damaged=src.copy()
    first=damaged[0].copy()
    first[4]+=1
    damaged[0]=first
    refused=False
    try:
        _=certify_shell_rows(damaged,core)
    except:
        refused=True
    assert_true(refused)
    # A forged child ID or missing source must be rejected.
    damaged=src.copy()
    first=damaged[0].copy()
    first[10]=0
    damaged[0]=first
    refused=False
    try:
        _=certify_shell_rows(damaged,core)
    except:
        refused=True
    assert_true(refused)
    damaged=src.copy()
    damaged[1]=damaged[0].copy()
    refused=False
    try:
        _=certify_shell_rows(damaged,core)
    except:
        refused=True
    assert_true(refused)
    require_contract("class-A d2 uniform fixed-constant shell: 518 extra strict overlaps, 259 each at offset sums +/-1, 1036 integer-polynomial strict margins, 518 uniformly valid n-affine proper-prefix choices with exact n-cancellation into the existing 80-state target and bound 5 for the 598 labelled states; malformed indices, source-sum, child, duplicate, zero-margin refusals; not an all-d2 hitting theorem")
