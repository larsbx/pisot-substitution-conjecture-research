"""Exact integer and cubic-number-field controls for C4 cyclic phase rank.

The block-cyclic matrices are SYNTHETIC and do not represent balanced words.
Tests verify hypotheses/conclusions of a conditional theorem, not C4/PSC.
"""
from itertools import combinations

M = [[1, 0, 1], [1, 2, 1], [0, 1, 1]]  # sigma=(01,112,012), PIP, det 2


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    assert len(a[0]) == len(b)
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def power(a, n):
    out = eye(len(a))
    for _ in range(n):
        out = mul(out, a)
    return out


def det3(a):
    (x, y, z), (p, q, r), (u, v, w) = a
    return x * (q*w-r*v) - y * (p*w-r*u) + z * (p*v-q*u)


def char3(a):
    b = mul(a, a)
    tr = sum(a[i][i] for i in range(3))
    tr2 = sum(b[i][i] for i in range(3))
    assert (tr*tr-tr2) % 2 == 0
    return (1, -tr, (tr*tr-tr2)//2, -det3(a))


def evaluate(poly, x):
    result = 0
    for c in poly:
        result = result * x + c
    return result


def has_integer_root(poly):
    constant = abs(poly[-1])
    if constant == 0:
        return True
    return any(evaluate(poly, sign*d) == 0
               for d in range(1, constant+1) if constant % d == 0
               for sign in (-1, 1))


def phase_lift(h):
    """P=[I,M,...,M^(h-1)]; N_(k+1,k)=I; N_(0,h-1)=M^h."""
    if h not in (2, 3, 4):
        raise ValueError("explicit algebraic period budget")
    size = 3*h
    p = [[0]*size for _ in range(3)]
    n = [[0]*size for _ in range(size)]
    phases = [j//3 for j in range(size)]
    for k in range(h):
        m_power = power(M, k)
        for i in range(3):
            for j in range(3):
                p[i][3*k+j] = m_power[i][j]
        step = eye(3) if k < h-1 else power(M, h)
        dest = (k+1) % h
        for i in range(3):
            for j in range(3):
                n[3*dest+i][3*k+j] = step[i][j]
    return p, n, phases


def _rank3_columns(p, columns):
    return any(det3([[p[row][j] for j in ids] for row in range(3)]) != 0
               for ids in combinations(columns, 3))


def audit_intertwiner_phase_minors(m, p, n, phases, h):
    """Fail closed on broken intertwining, fake phase, or low phase rank.

    DOES NOT establish literal word-realizability, SCC connectivity, or
    Pisot spectrum of a general provided integer M.
    """
    r = len(phases)
    if h < 1 or r < 3*h or r > 48 or len(m) != 3 or any(len(a)!=3 for a in m):
        raise ValueError("invalid phase/alphabet budget")
    if len(p) != 3 or any(len(a)!=r for a in p):
        raise ValueError("invalid Parikh matrix shape")
    if len(n) != r or any(len(a)!=r for a in n):
        raise ValueError("invalid child matrix shape")
    if any(x < 0 for row in m+p+n for x in row):
        raise ValueError("negative matrix entry")
    if any(k < 0 or k >= h for k in phases):
        raise ValueError("unknown phase label")
    if mul(p, n) != mul(m, p):
        raise ValueError("Parikh intertwiner failed")
    for parent in range(r):
        if not any(n[child][parent] for child in range(r)):
            raise ValueError("missing child column")
        for child in range(r):
            if n[child][parent] and phases[child] != (phases[parent]+1)%h:
                raise ValueError("incompatible phase edge")
    sizes = []
    for k in range(h):
        cols = [i for i in range(r) if phases[i] == k]
        sizes.append(len(cols))
        if len(cols) < 3 or not _rank3_columns(p, cols):
            raise ValueError("cyclic phase rank < 3")
    return sizes


def test_pisot_matrix_and_all_power_cubics_exact():
    assert power(M, 2) == [[1, 1, 2], [3, 5, 4], [1, 3, 2]]
    assert char3(M) == (1,-4,4,-2)
    assert det3(M) == 2
    expected = {
        1: (1,-4,4,-2),
        2: (1,-8,0,-4),
        3: (1,-22,-20,-8),
        4: (1,-64,-64,-16),
    }
    for h, polynomial in expected.items():
        a = power(M, h)
        assert char3(a) == polynomial
        assert not has_integer_root(polynomial)
        assert det3(a) == 2**h
        assert all(x > 0 for row in a for x in row) if h >= 2 else True


def test_exact_phase_rank_and_characteristic_block_divisibility():
    for h in (2,3,4):
        p, n, phases = phase_lift(h)
        assert mul(p,n) == mul(M,p)
        assert audit_intertwiner_phase_minors(M,p,n,phases,h) == [3]*h
        n_power = power(n,h)
        for k in range(h):
            block = [row[3*k:3*(k+1)] for row in n_power[3*k:3*(k+1)]]
            assert block == power(M,h)
            assert char3(block) == char3(power(M,h))
            parikh_block = [row[3*k:3*(k+1)] for row in p]
            assert det3(parikh_block) == 2**k
        for i in range(3*h):
            for j in range(3*h):
                if (i//3) != (j//3):
                    assert n_power[i][j] == 0
        assert len(n) == 3*h   # saturation, not a literal SCC


# Q[beta] = Q[t]/(t^3 - 4*t^2 + 4*t - 2), exact integer triples.
def scalar(v):
    return (v, 0, 0)


def add(x, y):
    return tuple(x[i]+y[i] for i in range(3))


def times(x, y):
    c = [0]*5
    for i in range(3):
        for j in range(3):
            c[i+j] += x[i]*y[j]
    for k in (4,3):
        z = c[k]
        c[k] = 0
        c[k-1] += 4*z
        c[k-2] -= 4*z
        c[k-3] += 2*z
    return tuple(c[:3])


def exponent(x, k):
    a = scalar(1)
    for _ in range(k):
        a = times(a,x)
    return a


def mv_poly(a, v):
    return [sum_poly([times(scalar(a[i][j]),v[j])
                      for j in range(len(v))])
            for i in range(len(a))]


def sum_poly(values):
    z = scalar(0)
    for val in values:
        z = add(z,val)
    return z


def test_exact_cubic_field_perron_equipartition():
    beta= (0,1,0)
    beta_minus_one = (-1,1,0)
    vm=[scalar(1), times(beta_minus_one,beta_minus_one),beta_minus_one]
    assert mv_poly(M,vm)==[times(beta,x) for x in vm]
    for h in (2,3,4):
        p,n,phases=phase_lift(h)
        weighted=[]
        for k in range(h):
            vk=[times(exponent(beta,h-1-k),x) for x in vm]
            pk=[row[3*k:3*k+3] for row in p]
            weighted.append(mv_poly(pk,vk))
        assert all(x==weighted[0] for x in weighted)
        assert weighted[0]==[times(exponent(beta,h-1),x) for x in vm]


def test_missing_children_wrong_phase_and_incorrect_parikh_refuse():
    p,n,phases=phase_lift(2)
    bad_n=[row.copy() for row in n]
    bad_n[3][0]=0
    # Each control names the check that refuses it. Only the last is a
    # budget/shape refusal (r=6 < 3h=9); the others are refused by the
    # intertwiner or phase-edge logic.
    for pp,nn,labels,h,reason in (
        (p,bad_n,phases,2,"Parikh intertwiner failed"),
        (p,n,[1]+phases[1:],2,"incompatible phase edge"),
        ([[p[i][j]+int(i==0 and j==3) for j in range(6)]
          for i in range(3)],n,phases,2,"Parikh intertwiner failed"),
        (p,n,phases,3,"invalid phase/alphabet budget"),
    ):
        try:
            audit_intertwiner_phase_minors(M,pp,nn,labels,h)
        except ValueError as exc:
            assert str(exc) == reason, (str(exc), reason)
        else:
            raise AssertionError("invalid periodic system accepted")


def test_real_strict_reducible_case_does_not_pass_rank_gate():
    # Complete strict four-state word system from #462: NOT PIP.
    m=[[1,1,0],[1,1,2],[0,1,1]]
    p=[[1,1,2,4],[1,3,4,6],[1,1,2,4]]
    n=[[0,0,3,5],[0,0,1,3],[1,0,1,1],[0,1,0,0]]
    assert mul(p,n)==mul(m,p)
    assert has_integer_root(char3(m))   # not irreducible cubic
    try:
        audit_intertwiner_phase_minors(m,p,n,[0]*4,1)
    except ValueError as exc:
        assert str(exc) == "cyclic phase rank < 3", str(exc)
    else:
        raise AssertionError("reducible rank-two strict fixture admitted")
