"""Independent exact integer oracle for phase-lattice index transport.

The input packets are SYNTHETIC, not valid literal balanced-pair SCCs.
No general C4, Rauzy measure or PSC statement follows from these tests.
"""
from itertools import combinations
from functools import reduce
from math import gcd

M2 = [[1,0,1],[1,2,1],[0,1,1]]  # det 2, primitive irreducible Pisot
M1 = [[1,1,1],[1,0,0],[0,1,0]]  # det 1, Tribonacci PIP


def eye(d=3):
    return [[int(i==j) for j in range(d)] for i in range(d)]


def mm(a,b):
    if len(a[0]) != len(b):
        raise ValueError("incorrect matrix dimensions")
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def mpow(m, n):
    result=eye(len(m))
    for _ in range(n):
        result=mm(result,m)
    return result


def det(a):
    (a0,a1,a2),(b0,b1,b2),(c0,c1,c2)=a
    return (a0*(b1*c2-b2*c1)-a1*(b0*c2-b2*c0)+a2*(b0*c1-b1*c0))


def phase_index(p, ids):
    if len(ids)<3:
        raise ValueError("phase has fewer than 3 columns")
    values=[]
    for cols in combinations(ids,3):
        values.append(abs(det([[p[i][j] for j in cols] for i in range(3)])))
    g=reduce(gcd, values, 0)
    if g==0:
        raise ValueError("phase rational Parikh rank <3")
    return g


def block2(m, x, y, a0, a1):
    """A_0 maps phase 0 -> 1, A_1 maps phase 1 -> 0."""
    p=[xx+yy for xx,yy in zip(x,y)]
    n=[[0]*6 for _ in range(6)]
    for i in range(3):
        for j in range(3):
            n[3+i][j]=a0[i][j]
            n[i][3+j]=a1[i][j]
    assert mm(p,n)==mm(m,p)
    return p,n,[0]*3+[1]*3


def audit(m,p,n,phase,h):
    """Necessary integer conditions only, NOT complete word closure.

    This independent oracle intentionally requires the caller to verify
    M is primitive irreducible Pisot and N's actual period/hypotheses.
    """
    if len(m)!=3 or any(len(row)!=3 for row in m):
        raise ValueError("not a ternary incidence matrix")
    if len(phase)<3*h or h<1 or h>8 or len(phase)>30:
        raise ValueError("invalid phase/size")
    r=len(phase)
    if len(p)!=3 or any(len(row)!=r for row in p):
        raise ValueError("invalid P")
    if len(n)!=r or any(len(row)!=r for row in n):
        raise ValueError("invalid N")
    if any(x<0 for row in m+p+n for x in row):
        raise ValueError("negative entry")
    if any(q<0 or q>=h for q in phase):
        raise ValueError("invalid phase label")
    mass=abs(det(m))
    if mass==0:
        raise ValueError("singular M")
    if mm(p,n)!=mm(m,p):
        raise ValueError("intertwiner failure")
    for j in range(r):
        if sum(p[i][j] for i in range(3))==0 or not any(n[i][j] for i in range(r)):
            raise ValueError("missing mass or child")
        if any(n[i][j] and phase[i]!=(phase[j]+1)%h for i in range(r)):
            raise ValueError("child phase mismatch")
    groups=[[i for i in range(r) if phase[i]==k] for k in range(h)]
    indices=[phase_index(p,ids) for ids in groups]
    transitions=[]
    for k in range(h):
        numerator=mass*indices[k]
        denominator=indices[(k+1)%h]
        if numerator%denominator:
            raise ValueError("nonintegral lattice transition")
        transitions.append(numerator//denominator)
    # The asserts below are algebraic identities once t_k=|m|g_k/g_(k+1) is
    # integral (cyclic cancellation); they are invariant checks, not controls.
    assert all(t>=1 for t in transitions)
    assert reduce(lambda a,b:a*b,transitions,1)==mass**h
    for t in transitions:
        probe=t
        common=gcd(probe,mass)
        while common>1:
            probe//=common
            common=gcd(probe,mass)
        assert probe==1, "unexpected prime outside determinant"
    if mass==1:
        assert indices==[indices[0]]*h
        assert transitions==[1]*h
    if r==3*h:
        for k in range(h):
            src,dst=groups[k],groups[(k+1)%h]
            block=[[n[i][j] for j in src] for i in dst]
            assert det(block)!=0 and abs(det(block))==transitions[k]
        assert reduce(lambda a,b:a*b, [det([[n[i][j] for j in groups[k]]
                         for i in groups[(k+1)%h]]) for k in range(h)],1)==det(m)**h
    return indices, transitions


def test_nonunit_all_three_exact_period_two_allocations():
    assert det(M2)==2
    power2=mpow(M2,2)
    pkt=[
        (eye(),M2,eye(),power2, [1,2],[1,4]),
        (power2,power2,M2,M2,[4,4],[2,2]),
        (M2,eye(),power2,eye(),[2,1],[4,1]),
    ]
    for x,y,a0,a1,expected_indices,expected_t in pkt:
        p,n,phase=block2(M2,x,y,a0,a1)
        assert audit(M2,p,n,phase,2)==(expected_indices,expected_t)
    assert sorted({(1,4),(2,2),(4,1)})==[(1,4),(2,2),(4,1)]


def test_unit_has_exact_lattice_equality_despite_all_positive_masses():
    assert det(M1)==1
    p0=mpow(M1,3)
    assert all(x>0 for row in p0 for x in row)
    p,n,phase=block2(M1,p0,p0,M1,M1)
    assert audit(M1,p,n,phase,2)==([1,1],[1,1])
    assert mm(M1,p0)==mm(p0,M1)


def test_nonunit_higher_phase_and_prime_support():
    # For P=[I,M,...,M^(h-1)] the last block is M^h:
    # each early t=1 and final t=|det M|^h.
    for h in (2,3,4):
        powers=[mpow(M2,k) for k in range(h)]
        p=[[powers[k][i][j] for k in range(h) for j in range(3)]
           for i in range(3)]
        n=[[0]*(3*h) for _ in range(3*h)]
        for k in range(h):
            block=eye() if k<h-1 else mpow(M2,h)
            for i in range(3):
                for j in range(3):
                    n[3*((k+1)%h)+i][3*k+j]=block[i][j]
        assert mm(p,n)==mm(M2,p)
        expected_g=[2**k for k in range(h)]
        expected_t=[1]*(h-1)+[2**h]
        assert audit(M2,p,n,[k for k in range(h) for _ in range(3)],h)==(
            expected_g,expected_t
        )


def test_broken_systems_and_real_strict_non_pisot_refuse():
    p,n,phase=block2(M2,eye(),M2,eye(),mpow(M2,2))
    samples=[]
    q=[row.copy() for row in p]
    q[0][3]+=1
    samples.append((M2,q,n,phase,2))
    nn=[row.copy() for row in n]
    nn[3][0]=0
    samples.append((M2,p,nn,phase,2))
    samples.append((M2,p,n,[1]+phase[1:],2))
    samples.append((M2,p,n,phase,3))
    samples.append(([[0]*3 for _ in range(3)],p,n,phase,2))
    for args in samples:
        try:
            audit(*args)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid integer lattice packet passed")
    # Genuine strict word-derived rank-2 control (M is reducible cubic).
    mr=[[1,1,0],[1,1,2],[0,1,1]]
    pr=[[1,1,2,4],[1,3,4,6],[1,1,2,4]]
    nr=[[0,0,3,5],[0,0,1,3],[1,0,1,1],[0,1,0,0]]
    assert mm(pr,nr)==mm(mr,pr)
    try:
        audit(mr,pr,nr,[0]*4,1)
    except ValueError as exc:
        assert "rank" in str(exc)
    else:
        raise AssertionError("rank-two reducible strict packet admitted")
