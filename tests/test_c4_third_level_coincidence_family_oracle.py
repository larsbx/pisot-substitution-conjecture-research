"""Independent exact Python oracle for a uniform Pisot strong-coincidence family.

The canonical bounded executable is Mojo. All examples here use literal word
inflation, exact prefix counters and complete balanced-factor decompositions;
finite tests do not prove the parameter-uniform algebraic statements.
"""
from collections import Counter
from itertools import combinations


def family(k: int):
    if not 1 <= k <= 32:
        raise ValueError("explicit bounded oracle budget")
    return ("01", "1" * k + "2" + "1" * k, "012")


def substitute(sigma, word):
    return "".join(sigma[int(a)] for a in word)


def third(sigma, a):
    word = str(a)
    for _ in range(3):
        word = substitute(sigma, word)
    return word


def actual_balanced_factors(top, bottom):
    if Counter(top) != Counter(bottom):
        raise ValueError("not balanced")
    first = Counter()
    second = Counter()
    result, start = [], 0
    for i, (a, b) in enumerate(zip(top, bottom), 1):
        first[a] += 1
        second[b] += 1
        if first == second:
            result.append((start, i, top[start:i], bottom[start:i]))
            first.clear()
            second.clear()
            start = i
    assert start == len(top) == len(bottom)
    return result


def det3(matrix):
    (a, b, c), (d, e, f), (g, h, i) = matrix
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def incidence(sigma):
    return [[w.count(str(row)) for w in sigma] for row in range(3)]


def test_simultaneous_pairwise_strong_coincidence():
    for k in range(1, 25):
        sigma = family(k)
        p = k * (2 * k + 1) + 1
        words = [third(sigma, i) for i in range(3)]
        assert all(p < len(w) and w[p] == "1" for w in words)
        prefixes = [tuple(w[:p].count(str(x)) for x in range(3))
                    for w in words]
        assert prefixes == [(1, 2*k*k, k)] * 3
        # Independent source identity, not a guessed first-letter quotient:
        A, B, C = sigma
        assert words[0] == A + B * (k + 1) + C + B * k
        assert words[2].startswith(words[0])
        assert words[1].startswith((B*k + C + B*k) * k)


def test_all_swaps_have_actual_diagonal_child_at_exact_cut():
    for k in range(1, 13):
        sigma = family(k)
        p = k * (2 * k + 1) + 1
        for a, b in combinations(range(3), 2):
            u, v = str(a)+str(b), str(b)+str(a)
            for _ in range(3):
                u, v = substitute(sigma, u), substitute(sigma, v)
            factors = actual_balanced_factors(u, v)
            assert any((start, end, x, y) == (p, p+1, "1", "1")
                       for start, end, x, y in factors)


def test_exact_incidence_and_spectral_integer_criteria():
    for k in range(1, 25):
        M = incidence(family(k))
        assert M == [[1, 0, 1], [1, 2*k, 1], [0, 1, 1]]
        assert det3(M) == 2*k
        square = [[sum(M[row][j]*M[j][col] for j in range(3))
                   for col in range(3)] for row in range(3)]
        assert square == [[1, 1, 2], [2*k+1, 4*k*k+1, 2*k+2],
                          [1, 2*k+1, 2]]
        # Direct determinant of (zI - M) agrees with the closed
        # cubic at independently chosen integer z values.
        def characteristic(z):
            return det3([[z*(i==j)-M[i][j] for j in range(3)]
                         for i in range(3)])
        def closed(z):
            return z*z*(z-2) - 2*k*(z-1)*(z-1)
        for z in (-3, -1, 0, 1, 2, 2*k, 2*k+1, 2*k+3):
            assert characteristic(z) == closed(z)
        assert closed(2*k) == -2*k
        assert closed(2*k+1) == 4*k*k-2*k-1 > 0
        assert -4*k*(8*k*k-13*k+16) < 0
        # Bounded root sanity check; the uniform irreducibility proof
        # is the number-theoretic gcd argument in the dated math note.
        assert all(closed(z) != 0 for z in range(-2*k, 2*k+3))


def test_refuse_invalid_or_excessive_parameters():
    for k in (-3, -1, 0, 33, 500000):
        try:
            family(k)
        except ValueError:
            continue
        raise AssertionError("invalid family budget accepted")


def test_k_one_has_earlier_level_two_simultaneous_coincidence():
    sigma = family(1)  # 01/121/012, the exact singleton in PR #475.
    words = [substitute(sigma, sigma[i]) for i in range(3)]
    assert words == ["01121", "121012121", "01121012"]
    assert all(w[4] == "1" for w in words)
    assert [tuple(w[:4].count(str(a)) for a in range(3)) for w in words] == [
        (1, 2, 1), (1, 2, 1), (1, 2, 1)
    ]


def asymmetric_family(left, right):
    """Independent two-parameter literal images, with a hard oracle budget."""
    if not (1 <= left <= 24 and 1 <= right <= 24):
        raise ValueError("invalid/over-cap asymmetric run")
    return ("01", "1"*left + "2" + "1"*right, "012")


def test_all_asymmetric_literal_prefixes_and_symmetry_backcompat():
    for left in range(1, 13):
        for right in range(1, 13):
            sig = asymmetric_family(left, right)
            p = left * (left + right + 1) + 1
            pref = (1, left * (left + right), left)
            words = [third(sig, letter) for letter in range(3)]
            assert all(w[p] == "1" and
                       tuple(w[:p].count(str(i)) for i in range(3)) == pref
                       for w in words)
            if left == right:
                assert sig == family(left)
                assert p == left * (2*left + 1) + 1


def test_asymmetric_all_three_swap_factors_are_actual_diagonals():
    for left in range(1, 7):
        for right in range(1, 7):
            sig = asymmetric_family(left, right)
            p = left*(left+right+1)+1
            for a, b in combinations(range(3), 2):
                u, v = str(a)+str(b), str(b)+str(a)
                for _ in range(3):
                    u, v = substitute(sig,u), substitute(sig,v)
                factors = actual_balanced_factors(u,v)
                assert (p,p+1,"1","1") in factors


def test_same_incidence_but_distinct_literal_common_addresses():
    # Each split has identical M_s for s=4; the *address* depends on
    # left_run, which incidence/Perron/Parikh data alone cannot recover.
    fixed_s=4
    Ms=[]
    cuts=[]
    for left in (1,2,3):
        sig=asymmetric_family(left,fixed_s-left)
        Ms.append(incidence(sig))
        words=[third(sig,i) for i in range(3)]
        cut=left*(fixed_s+1)+1
        cuts.append(cut)
        assert all(tuple(w[:cut].count(str(j)) for j in range(3))
                   == (1,left*fixed_s,left) and w[cut]=="1" for w in words)
    assert Ms == [Ms[0]]*3
    assert cuts == [6,11,16]


def test_asymmetric_generalized_pisot_integer_data():
    for left in range(1,9):
        for right in range(1,9):
            s=left+right
            matrix=incidence(asymmetric_family(left,right))
            assert matrix==[[1,0,1],[1,s,1],[0,1,1]]
            assert det3(matrix)==s
            square=[[sum(matrix[i][t]*matrix[t][j] for t in range(3))
                      for j in range(3)] for i in range(3)]
            assert square==[[1,1,2],[s+1,s*s+1,s+2],[1,s+1,2]]
            assert all(all(x>0 for x in row) for row in square)
            def F(z):
                return z*z*(z-2)-s*(z-1)*(z-1)
            assert F(s)==-s
            assert F(s+1)==s*s-s-1>0
            assert -s*(4*s*s-13*s+32)<0
            assert all(F(n)!=0 for n in range(-s,s+3))


def test_asymmetric_parameter_budget_fails_closed():
    for a,b in ((-1,1),(0,2),(2,0),(2,-1),(25,2),(2,25)):
        try:
            asymmetric_family(a,b)
        except ValueError:
            continue
        raise AssertionError("malformed asymmetric family admitted")
