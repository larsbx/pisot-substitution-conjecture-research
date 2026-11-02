"""Exact nonunit M-adic Class-A digit normal form, scoped finite controls."""

from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_a_madic_digits import (
    MAdicDigits, parameters, apply_incidence, invert_image,
    extract_digits, reconstruct_digits, in_image_power, same_power_coset,
    recover_zero_parent,
)


def reject_inverse(k: Int,t: Int,v: List[Int]) -> Bool:
    try:
        _ = invert_image(k,t,v)
        return False
    except:
        return True


def main() raises:
    var specimens=0
    var cosets=0
    for k in range(4):
        for t in range(4):
            var par=parameters(k,t)
            var n=par[0]
            var d=par[1]
            assert_equal(n,k+t+3)
            assert_equal(d,k+2*t+5)
            assert_true(reject_inverse(k,t,[1,0,0]))
            for a in range(-2,3):
                for b in range(-2,3):
                    for c in range(-2,3):
                        var v: List[Int]=[a,b,c]
                        for level in range(5):
                            var code=extract_digits(k,t,v,level)
                            var got=reconstruct_digits(k,t,code)
                            assert_equal(got[0],a)
                            assert_equal(got[1],b)
                            assert_equal(got[2],c)
                            var allzero=True
                            for bit in code.bits:
                                if bit!=0:
                                    allzero=False
                            assert_true(in_image_power(k,t,v,level)==allzero)
                            specimens+=1
            # Every declared M^level parent offset is uniquely decoded from
            # the exact proper-prefix-difference lattice coordinate.
            var original: List[Int] = [1,-2,3]
            var forward = original.copy()
            for level in range(1,5):
                forward=apply_incidence(k,t,forward)
                var decoded=recover_zero_parent(k,t,forward,level)
                assert_equal(decoded[0],original[0])
                assert_equal(decoded[1],original[1])
                assert_equal(decoded[2],original[2])
            refused=False
            try:
                _=recover_zero_parent(k,t,[1,0,0],1)
            except:
                refused=True
            assert_true(refused)

            # Exhaustively enumerate the full index-2^level quotient without
            # asserting any cyclic group structure for this finite cokernel.
            for level in range(1,5):
                var seen=List[List[Int]]()
                for code in range(1<<level):
                    var bits=List[Int]()
                    for j in range(level):
                        bits.append((code>>j)&1)
                    var record=MAdicDigits(bits,[0,0,0])
                    var representative=reconstruct_digits(k,t,record)
                    var check=extract_digits(k,t,representative,level)
                    for j in range(level):
                        assert_equal(check.bits[j],bits[j])
                    assert_equal(check.tail[0],0)
                    assert_equal(check.tail[1],0)
                    assert_equal(check.tail[2],0)
                    for other in seen:
                        assert_true(not same_power_coset(k,t,representative,other,level))
                    seen.append(representative)
                    cosets+=1
                assert_equal(len(seen),1<<level)

            # The same residue class need not have the same integer vector.
            # Subtract one full level-two M² translation to verify actual
            # quotient equivalence rather than equality.
            var v: List[Int]=[2,-3,1]
            var drift=apply_incidence(k,t,apply_incidence(k,t,[1,-1,2]))
            var moved: List[Int]=[v[0]+drift[0],v[1]+drift[1],v[2]+drift[2]]
            assert_true(same_power_coset(k,t,v,moved,2))
            assert_true(not same_power_coset(k,t,v,[v[0]+1,v[1],v[2]],2))

    var bad_bits: List[Int]=[0,2]
    var malformed=MAdicDigits(bad_bits,[0,0,0])
    var refused=False
    try:
        _=reconstruct_digits(0,0,malformed)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=extract_digits(0,0,[0,0,0],65)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=parameters(-1,0)
    except:
        refused=True
    assert_true(refused)
    print("CLASS_A_MADIC_DIGITS_PASS",specimens,cosets)
    require_contract("ClassA exact unique finite-place 2-adic digit normal form and 2^m coset certificates at finite levels; no automatic occurrence legal hitting, nonunit realizability or PSC")
