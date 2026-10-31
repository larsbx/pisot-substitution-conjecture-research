"""Exact native full-Parikh injectivity and cubic beta-intertwining."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.perron_field3 import CubicElt, PerronField3
from psc.class_a_parikh_field_bridge import (
    class_a_parameters, check_minus_class_a_field, class_a_lengths,
    parikh_shift, decode_parikh_shift, verify_class_a_intertwining,
    verify_indexed_parikh_child,
)

def rejects_wrong_field(field: PerronField3, n: Int, d: Int) -> Bool:
    try:
        check_minus_class_a_field(field,n,d)
        return False
    except:
        return True

def main() raises:
    var count = 0
    for k in range(7):
        for t in range(5):
            var vals=class_a_parameters(k,t)
            var n=vals[0]
            var d=vals[1]
            var A=vals[2]
            assert_equal(A,n+d)
            var field=PerronField3(2,n-d-1,-n-2)
            check_minus_class_a_field(field,n,d)
            var lens=class_a_lengths(d)
            assert_equal(lens.l0,parikh_shift(d,1,0,0))
            assert_equal(lens.l1,parikh_shift(d,0,1,0))
            assert_equal(lens.l2,parikh_shift(d,0,0,1))
            for p in range(-3,4):
                for q in range(-2,3):
                    for r in range(-2,3):
                        verify_class_a_intertwining(field,n,d,p,q,r)
                        var coeff=parikh_shift(d,p,q,r)
                        var decoded=decode_parikh_shift(d,coeff)
                        assert_equal(decoded[0],p)
                        assert_equal(decoded[1],q)
                        assert_equal(decoded[2],r)
                        assert_equal(coeff.is_zero(),p==0 and q==0 and r==0)
                        count+=1
            # X(d+1,0)->Q: top x RUN(d+1), prefix=(1,0,d).
            verify_indexed_parikh_child(field,n,d,1,0,-1,
                1,0,d,0,0,0,0,-1,1)
            assert_true(rejects_wrong_field(PerronField3(2,n-d,-n-2),n,d))
            var bad=False
            try:
                _=decode_parikh_shift(d,CubicElt(1,0,0))
            except:
                bad=True
            assert_true(bad)
            bad=False
            try:
                verify_indexed_parikh_child(field,n,d,1,0,-1,
                    1,0,d,0,0,0,0,-1,2)
            except:
                bad=True
            assert_true(bad)
    # An exact matching polynomial at (n,d) need not define an actual
    # member of the k,t>=0 minus chamber. Refuse those false inputs.
    assert_true(rejects_wrong_field(PerronField3(2,-4,-5),3,6))
    assert_true(rejects_wrong_field(PerronField3(2,-2,-6),4,5))
    assert_equal(count,7*5*7*5*5)
    print('CLASS_A_PARIKH_FIELD_BRIDGE_EXACT_PASS',count)
    require_contract("minus class-A regression specimens: research-normalized Parikh lattice inverse, beta intertwining, supplied-prefix transport and invalid-input refusal")
