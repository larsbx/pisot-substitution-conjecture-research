"""Independent integer-minor Smith audit, no imported symbolic identity.

Computes M^m by generic matrix multiplication and determinantal divisors:
D1=gcd(entries), D2=gcd(all 2x2 minors), D3=abs(det).
This deliberately does NOT implement the native closed-form proof.
"""
from functools import reduce
from itertools import combinations
from math import gcd
import pytest


def matrix(k,t):
    n=k+t+3
    d=k+2*t+5
    return ((2,1,1),(0,1,1),(n+d,n,n-1))


def product(a,b):
    return tuple(tuple(sum(a[i][h]*b[h][j] for h in range(3))
                       for j in range(3)) for i in range(3))


def power(a,m):
    out=((1,0,0),(0,1,0),(0,0,1))
    for _ in range(m):
        out=product(out,a)
    return out


def det(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def smith(a):
    d1=reduce(gcd,(abs(x) for row in a for x in row),0)
    minors=[]
    for rows in combinations(range(3),2):
        for cols in combinations(range(3),2):
            i,j=rows
            p,q=cols
            minors.append(abs(a[i][p]*a[j][q]-a[i][q]*a[j][p]))
    d2=reduce(gcd,minors,0)
    d3=abs(det(a))
    assert d1 and d2 and d3 and d2%d1==0 and d3%d2==0
    result=(d1,d2//d1,d3//d2)
    assert result[1]%result[0]==0 and result[2]%result[1]==0
    return result


def predicted(k,t,m):
    if t%2==0:
        return (1,1,2**m)
    if k%2==0:
        q,r=divmod(m,3)
        if r==0:return (2**q,2**q,2**q)
        if r==1:return (2**q,2**q,2**(q+1))
        return (2**q,2**(q+1),2**(q+1))
    q,r=divmod(m,2)
    if r==0:return (1,2**q,2**q)
    return (1,2**q,2**(q+1))


@pytest.mark.parametrize("k",range(6))
@pytest.mark.parametrize("t",range(6))
def test_independent_determinantal_divisors(k,t):
    a=matrix(k,t)
    assert det(a)==-2
    for m in range(9):
        actual=smith(power(a,m))
        assert actual==predicted(k,t,m)
        assert actual[0]*actual[1]*actual[2]==2**m


def mod2_rank(a):
    b=[[x%2 for x in row] for row in a]
    pivot=0
    for col in range(3):
        row=next((r for r in range(pivot,3) if b[r][col]),None)
        if row is None:continue
        b[pivot],b[row]=b[row],b[pivot]
        for r in range(3):
            if r!=pivot and b[r][col]:
                b[r]=[(x^y) for x,y in zip(b[r],b[pivot])]
        pivot+=1
    return pivot


@pytest.mark.parametrize("k,t",[(0,0),(1,0),(0,1),(1,1),(2,3)])
def test_genuine_distinct_2adic_regimes(k,t):
    a=matrix(k,t)
    if t%2==0:
        assert all(mod2_rank(power(a,m))==2 for m in range(1,8))
    elif k%2==0:
        assert [mod2_rank(power(a,m)) for m in (1,2,3)]==[2,1,0]
        # M^3/2 is an *integer* unimodular matrix.
        cube=power(a,3)
        assert all(x%2==0 for row in cube for x in row)
        assert abs(det(tuple(tuple(x//2 for x in row) for row in cube)))==1
    else:
        assert [mod2_rank(power(a,m)) for m in (1,2,3)]==[2,1,1]


def test_binary_coset_transversal_not_always_cyclic_group():
    assert predicted(0,0,3)==(1,1,8)
    assert predicted(0,1,3)==(2,2,2)
    assert predicted(1,1,3)==(1,2,4)
    assert predicted(1,1,6)==(1,8,8)


@pytest.mark.parametrize("k,t",[(0,0),(1,0),(0,1),(1,1)])
def test_mod2_cyclic_basis_witness(k,t):
    a=matrix(k,t)
    if t%2: v=(1,0,0)
    elif k%2==0: v=(0,1,0)
    else: v=(0,1,1)
    def action(x):
        return tuple(sum(a[i][j]*x[j] for j in range(3))
                     for i in range(3))
    u=action(v)
    w=action(u)
    krylov=tuple((v[i],u[i],w[i]) for i in range(3))
    assert det(krylov)%2==1
