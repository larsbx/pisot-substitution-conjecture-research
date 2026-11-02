"""Native group-structure Smith checks against preexisting arbitrary-Q kernel."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_a_madic_smith import (
    predicted_smith, class_a_integer_matrix,
    certify_smith_against_generic, cyclic_krylov_mod2,
)

def main() raises:
    var certificates=0
    for k in range(4):
        for t in range(4):
            assert_true(cyclic_krylov_mod2(k,t))
            var entries=class_a_integer_matrix(k,t)
            assert_equal(len(entries),9)
            for m in range(6):
                var factors=certify_smith_against_generic(k,t,m)
                assert_equal(factors[0]*factors[1]*factors[2],1 << m)
                assert_true(factors[1]%factors[0]==0)
                assert_true(factors[2]%factors[1]==0)
                if t%2==0:
                    assert_equal(factors[0],1)
                    assert_equal(factors[1],1)
                elif k%2==0 and m>=3:
                    assert_true(factors[0]>1)
                elif k%2==1:
                    assert_equal(factors[0],1)
                certificates+=1
    # Boundary cases: exact zero level, non-cyclic rank-3/2 split,
    # cyclic group for all even-t values, and fail-closed budgets.
    var even=predicted_smith(9,8,15)
    assert_equal(even[2],1<<15)
    var cubic=predicted_smith(8,9,8)
    assert_equal(cubic[0],4)
    assert_equal(cubic[1],8)
    assert_equal(cubic[2],8)
    var quadratic=predicted_smith(9,7,9)
    assert_equal(quadratic[0],1)
    assert_equal(quadratic[1],16)
    assert_equal(quadratic[2],32)
    var refused=False
    try:
        _=predicted_smith(-1,0,1)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=predicted_smith(0,0,31)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=certify_smith_against_generic(0,1,7)
    except:
        refused=True
    assert_true(refused)
    print("CLASS_A_MADIC_SMITH_PASS",certificates)
    require_contract("Class-A finite-level exact Smith trichotomy and cyclic local basis; generic arbitrary-precision independent Smith replay; no BH, entry or realized-overlap conclusion")
