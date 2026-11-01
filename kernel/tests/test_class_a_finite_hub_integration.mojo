"""Finite graph completeness and missing/escaping extension controls."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_finite_hub_integration import finite_hub_audit, finite_extension_criterion

def main() raises:
    for mode in [4,9]:
        var out=finite_hub_audit(mode,0,0)
        assert_true(out[0]>0 and out[3]==1 and out[4]==0 and out[5]==2)
    var refused=False
    try:
        _=finite_hub_audit(9,0,0,1)
    except:
        refused=True
    assert_true(refused)
    assert_true(finite_extension_criterion([[1],[1],[0]], [0,2], 0, 2))
    assert_true(not finite_extension_criterion([[1],[1],[3],[3]], [0,2], 0, 2))
    assert_true(not finite_extension_criterion([[1],[1],[0],[3]], [0,2,3], 0, 2))
    require_contract("finite minus class-A k,t=0..3 four/nine-seed hub graphs: exact original native normalization, complete occurrence adjacency, typed terminals, reverse productivity and X access, recurrent/bad-sink SCCs and nine-seed S1 exception; capped graphs and missing/escaping extension hypotheses refuse; no universal BH or PSC theorem")
