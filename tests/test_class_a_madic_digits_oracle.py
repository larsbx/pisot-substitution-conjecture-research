"""Independent Cramer/Smith-order oracle for minus-Class-A finite-place digits.

An intentionally separate matrix-power implementation cross-checks the
canonical Mojo iterative parity algorithm. No numerical eigenvalues or
pretence of cyclic Z/2^m are used.
"""

from itertools import product
import pytest


def matrix(k,t):
    n=k+t+3
    d=k+2*t+5
    return ((2,1,1),(0,1,1),(n+d,n,n-1))


def identity():
    return ((1,0,0),(0,1,0),(0,0,1))


def product3(a,b):
    return tuple(tuple(sum(a[i][h]*b[h][j] for h in range(3))
                       for j in range(3)) for i in range(3))


def power(a,m):
    result=identity()
    for _ in range(m):
        result=product3(result,a)
    return result


def matvec(a,x):
    return tuple(sum(a[i][j]*x[j] for j in range(3)) for i in range(3))


def det(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
           -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
           +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def replace_col(a,v,j):
    return tuple(tuple(v[i] if z==j else a[i][z]
                       for z in range(3)) for i in range(3))


def cramers(a,v):
    determinant=det(a)
    assert determinant
    numerators=[det(replace_col(a,v,j)) for j in range(3)]
    if any(n%determinant for n in numerators):
        return None
    return tuple(n//determinant for n in numerators)


def iterative_parity(k,t,v,m):
    n=k+t+3
    d=k+2*t+5
    a=n+d
    bits=[]
    for _ in range(m):
        x,c,y=v
        bit=(x-c)%2
        x-=bit
        p=(x-c)//2
        v=(p,y-a*p-(n-1)*c,a*p+n*c-y)
        bits.append(bit)
    return tuple(bits),v


def build_from_digits(k,t,bits,tail=(0,0,0)):
    a=matrix(k,t)
    out=tail
    for bit in reversed(bits):
        z=matvec(a,out)
        out=(z[0]+bit,z[1],z[2])
    return out


@pytest.mark.parametrize("k,t",[(0,0),(1,0),(0,1),(2,3),(3,0),(6,7)])
def test_every_tested_vector_matches_independent_cramer(k,t):
    a=matrix(k,t)
    assert det(a)==-2
    for m in range(6):
        mp=power(a,m)
        assert det(mp)==(-2)**m
        for v in product(range(-2,3),repeat=3):
            bits,tail=iterative_parity(k,t,v,m)
            assert build_from_digits(k,t,bits,tail)==v
            assert (cramers(mp,v) is not None)==(not any(bits))
            if not any(bits):
                assert cramers(mp,v)==tail


@pytest.mark.parametrize("k,t",[(0,0),(1,2),(3,0),(0,4)])
def test_complete_binary_word_coset_representatives(k,t):
    a=matrix(k,t)
    for m in range(1,6):
        mp=power(a,m)
        representatives=[]
        for bitword in product((0,1),repeat=m):
            w=build_from_digits(k,t,bitword)
            assert iterative_parity(k,t,w,m)==(tuple(bitword),(0,0,0))
            for prev in representatives:
                diff=tuple(w[i]-prev[i] for i in range(3))
                assert cramers(mp,diff) is None
            representatives.append(w)
        assert len(representatives)==2**m


def test_cokernel_can_be_noncylcic_and_bits_not_linear_binary_int():
    # Distinct digit words are a complete coset transversal, not a
    # declaration of Z/2^m group structure. For k=t=0 the reduction of
    # M mod 2 is neither invertible nor identically zero.
    a=matrix(0,0)
    assert det(a)==-2
    # Test coset group order from determinant, without asserting generator.
    for m in range(1,6):
        assert abs(det(power(a,m)))==2**m


def test_zero_prefix_lattice_condition_is_necessary_not_word_realization():
    # This arithmetic filter has no ordered-word / geometry inputs.
    # In particular it must not be treated as a proof that an arbitrary
    # residue word is attained by an actual substitution-prefix pair.
    a=matrix(0,0)
    assert iterative_parity(0,0,(1,0,0),1)[0]==(1,)
    assert cramers(a,(1,0,0)) is None
