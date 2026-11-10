"""Independent literal-word/integer-matrix oracle for one-step Class-A zeros.

This oracle intentionally does not import the Mojo formulas or the optimized
graph builder. All propositions concern one actual substitution level only.
"""
import itertools
import pytest


def words(k, t):
    n = k+t+3
    d = k+2*t+5
    return ((0,)+(2,)*(n+d)+(0,),
            (1,)+(2,)*n+(0,),
            (0,)+(2,)*(n-1)+(1,))


def matrix_image(k,t,v):
    n=k+t+3
    d=k+2*t+5
    p,q,r=v
    return (2*p+q+r, q+r, (n+d)*p+n*q+(n-1)*r)


def prefix(word,index):
    return tuple(word[:index].count(s) for s in range(3))


def literal_child(k,t,top,bottom,offset,i,j):
    sigma=words(k,t)
    pt=prefix(sigma[top],i)
    pb=prefix(sigma[bottom],j)
    mw=matrix_image(k,t,offset)
    return (sigma[top][i],sigma[bottom][j],
            tuple(mw[r]+pb[r]-pt[r] for r in range(3)))


def formula(k,t,top,bottom,offset):
    n=k+t+3
    d=k+2*t+5
    p,q,r=offset
    f=lambda a: 1 if a!=1 else 0
    delta=f(top)-f(bottom)
    first=(p,q,r)==(0,0,0)
    if p!=delta or p+q+r!=0:
        return first, ()
    gap=q+(d+1)*delta
    lo=max(1,1+gap)
    hi=min(len(words(k,t)[top])-1,len(words(k,t)[bottom])-1+gap)
    return first, tuple((i,i-gap) for i in range(lo,hi+1))


@pytest.mark.parametrize("k,t",[(0,0),(0,1),(1,0),(1,2),(3,0),(0,4),(5,7)])
def test_every_literal_prefix_pair_has_unique_zero_parent(k,t):
    sigma=words(k,t)
    assert len(sigma)==3
    n=k+t+3
    d=k+2*t+5
    assert matrix_image(k,t,(1,0,0))==(2,0,n+d)
    assert matrix_image(k,t,(0,1,0))==(1,1,n)
    assert matrix_image(k,t,(0,0,1))==(1,1,n-1)
    # Exact determinant = -2; the image lattice has parity X-C even.
    for top,bottom in itertools.product(range(3),repeat=2):
        for i,j in itertools.product(range(len(sigma[top])),range(len(sigma[bottom]))):
            pt=prefix(sigma[top],i)
            pb=prefix(sigma[bottom],j)
            diff=tuple(a-b for a,b in zip(pt,pb))
            if (i==0)!=(j==0):
                assert (diff[0]-diff[1])%2==1
                continue
            delta=(top!=1)-(bottom!=1) if i and j else 0
            diff_index=i-j
            offset=(delta,diff_index-(d+1)*delta,
                    -diff_index+d*delta)
            assert matrix_image(k,t,offset)==diff
            assert literal_child(k,t,top,bottom,offset,i,j)[2]==(0,0,0)
            first,addresses=formula(k,t,top,bottom,offset)
            assert (i,j) in addresses if i and j else first
            # A different full-Parikh offset cannot counterfeit the hit.
            changed=(offset[0],offset[1],offset[2]+1)
            assert literal_child(k,t,top,bottom,changed,i,j)[2]!=(0,0,0)


@pytest.mark.parametrize("k,t",[(0,0),(1,2),(3,0),(0,3)])
def test_interval_equals_all_real_indexed_hits(k,t):
    sigma=words(k,t)
    for top,bottom in itertools.product(range(3),repeat=2):
        for v in itertools.product(range(-2,3),repeat=3):
            first,interval=formula(k,t,top,bottom,v)
            predicted=set(interval)
            if first: predicted.add((0,0))
            observed={(i,j) for i,j in itertools.product(
                range(len(sigma[top])),range(len(sigma[bottom])))
                if literal_child(k,t,top,bottom,v,i,j)[2]==(0,0,0)}
            assert observed==predicted


def test_hub_and_nonclaims():
    for k,t in ((0,0),(1,2),(17,9)):
        assert formula(k,t,0,0,(1,0,-1))==(False,())
        # A zero-shift c/x parent has only a FIRST/FIRST zero shift,
        # which has distinct letter types and is NOT typed coincidence.
        first,positive=formula(k,t,1,0,(0,0,0))
        assert first and not positive
        assert literal_child(k,t,1,0,(0,0,0),0,0)==(1,0,(0,0,0))
        # Algebraic zero descendants do not themselves prove that the
        # formal parent is a strict geometrical overlap.


@pytest.mark.parametrize("k,t",[(0,0),(1,2),(3,0),(0,3),(5,7)])
def test_nine_affine_predecessor_strips_exact_set_and_cardinality(k,t):
    n=k+t+3
    d=k+2*t+5
    sigma=words(k,t)
    R=[len(w)-2 for w in sigma]
    predicted=set()
    for top,bottom in itertools.product(range(3),repeat=2):
        delta=int(top!=1)-int(bottom!=1)
        predicted.add((top,bottom,0,0,0))
        for gap in range(-R[bottom],R[top]+1):
            predicted.add((top,bottom,delta,
                           gap-(d+1)*delta,-gap+d*delta))
    assert len(predicted)==18*n+6*d+7
    assert len([v for v in predicted if any(v[2:])])==18*n+6*d-2
    # Rebuild the entire inverse-target set from independent real prefix
    # pairs, rather than the strip endpoints or a copied closed formula.
    actual=set()
    for top,bottom in itertools.product(range(3),repeat=2):
        for i,j in itertools.product(range(len(sigma[top])),
                                     range(len(sigma[bottom]))):
            pt=prefix(sigma[top],i)
            pb=prefix(sigma[bottom],j)
            diff=[x-y for x,y in zip(pt,pb)]
            if (diff[0]-diff[1])%2:
                continue
            p=(diff[0]-diff[1])//2
            r=(n+d)*p+n*diff[1]-diff[2]
            q=diff[1]-r
            candidate=(top,bottom,p,q,r)
            assert literal_child(k,t,top,bottom,(p,q,r),i,j)[2]==(0,0,0)
            actual.add(candidate)
    assert actual==predicted
