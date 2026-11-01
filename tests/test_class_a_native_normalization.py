import pytest
from reference.psc_research import class_a_native_normalization as x

def test_native_cross_and_scalar_coefficient_identity():
    for k in range(13):
        for t in range(9):
            n,d,A=x.params(k,t)
            assert x.normalize(n,d)==x.native_lengths(n,d)
            assert x.actual_cross_product(n,d)==x.native_lengths(n,d)
            assert tuple(x.mul(x.native_scale(n,d),z,n,d) for z in x.normalized_lengths(n,d))==x.native_lengths(n,d)

def test_exact_native_parikh_lattice_index_and_two_divisibility_guards():
    checked=0
    for k in range(13):
        for t in range(9):
            n,d,A=x.params(k,t)
            for p in (-3,-1,0,2):
                for q in (-2,0,3):
                    for r in (-1,0,1,4):
                        w=(p,q,r)
                        assert x.decode_native(n,d,x.native_shift(n,d,*w))==w
                        assert (x.native_shift(n,d,*w)==(0,0,0))==(w==(0,0,0))
                        assert x.native_shift(n,d,*x.incidence(n,d,w))==x.beta_times(x.native_shift(n,d,*w),n,d)
                        checked+=1
            with pytest.raises(ValueError):x.decode_native(n,d,(1,0,0))
            with pytest.raises(ValueError):x.decode_native(n,d,(0,d,0))
    assert checked==5616

def test_real_indexed_literal_child_transport_and_reversal():
    total=0
    for k in range(5):
        for t in range(5):
            W=x.words(k,t)
            for w in ((0,0,1,0,-1),(0,0,0,1,0),(1,2,0,-2,2),(2,2,1,-1,-1)):
                rw=(w[1],w[0],-w[2],-w[3],-w[4])
                for i in range(len(W[w[0]])):
                    for j in range(len(W[w[1]])):
                        child,shift=x.indexed(k,t,w,i,j)
                        rev,rshift=x.indexed(k,t,rw,j,i)
                        assert rev==(child[1],child[0],-child[2],-child[3],-child[4])
                        assert rshift==tuple(-v for v in shift)
                        total+=1
    assert total>20000

def test_wrong_parameter_and_typed_occurrence_fail_closed():
    with pytest.raises(ValueError):x.params(-1,0)
    with pytest.raises(ValueError):x.normalize(3,6)
    with pytest.raises(ValueError):x.normalize(4,5)
    with pytest.raises(ValueError):x.indexed(0,0,(0,1,0,0,0),100,0)
    with pytest.raises(ValueError):x.indexed(0,0,(3,1,0,0,0),0,0)
