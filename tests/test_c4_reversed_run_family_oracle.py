"""Independent literal oracle for the reversed closed-run Pisot family.

Paper proof: docs/c4-reversed-run-family-four-level-coincidence-2026-11-04.md.
A finite test is not a proof of the unbounded symbolic formulas.
"""
from collections import Counter
from itertools import combinations


def family(a, b):
    if a < 0 or b < 0 or a + b == 0 or a > 8 or b > 8 or a + b > 12:
        raise ValueError("bounded reversed-run input refused")
    return ("10", "1" * b + "2" + "1" * a, "210")


def inflate(sig, word, n):
    for _ in range(n):
        word = "".join(sig[int(c)] for c in word)
    return word


def cert(a, b):
    s = a + b
    if b == 0:
        return 2, 0, (0, 0, 0), "2"
    if a == 0:
        if b == 1:
            return 4, 9, (2, 4, 3), "2"
        return 4, b**3 + b*b + 5*b + 6, (
            b + 2, b**3 + 3*b + 2, b*b + b + 2), "2"
    if b == 1:
        return 3, a + 5, (1, a + 2, 2), "1"
    return 4, b*(s*s + 2*s + 4) + 2*s + 10, (
        b + 3, b*s*s + b*s + 2*s + b + 3, b*s + 2*b + 4), "1"


def parikh(word):
    return tuple(word.count(c) for c in "012")


def factor(top, bottom):
    assert len(top) == len(bottom) and parikh(top) == parikh(bottom)
    a, b = Counter(), Counter()
    out, start = [], 0
    for k, (c, d) in enumerate(zip(top, bottom), 1):
        a[c] += 1
        b[d] += 1
        if a == b:
            out.append((start, k, top[start:k], bottom[start:k]))
            a.clear()
            b.clear()
            start = k
    assert start == len(top)
    return out


def test_uniform_bounded_parameter_quadrant():
    for a in range(9):
        for b in range(9):
            if a + b == 0 or a + b > 12:
                continue
            sig = family(a, b)
            n, p, Q, z = cert(a, b)
            assert n <= 4 and p == sum(Q)
            words = [inflate(sig, str(j), n) for j in range(3)]
            assert all(p < len(w) and w[p] == z and parikh(w[:p]) == Q
                       for w in words)
            assert sig == tuple(x[::-1] for x in
                                ("01", "1"*a+"2"+"1"*b, "012"))


def test_four_level_word_identities_and_explicit_substrings():
    for a in range(9):
        for b in range(9):
            if a + b == 0 or a + b > 12:
                continue
            sig = family(a, b)
            A, B, C = sig
            F, G, H = B + A, B*b + C + B*a, C + B + A
            assert [inflate(sig, str(i), 2) for i in range(3)] == [F, G, H]
            assert [inflate(sig, str(i), 3) for i in range(3)] == [
                G + F, G*b + H + G*a, H + G + F]
            words4 = [G*b+H+G*(a+1)+F,
                      (G*b+H+G*a)*b+(H+G+F)+(G*b+H+G*a)*a,
                      (H+G+F)+(G*b+H+G*a)+(G+F)]
            assert words4 == [inflate(sig, str(i), 4) for i in range(3)]
            n, p, Q, z = cert(a, b)
            if b == 0:
                assert all(inflate(sig, str(i), 2).startswith("2")
                           for i in range(3))
            elif a >= 1 and b == 1:
                assert p == len(B+C)
                assert parikh(B+C) == parikh(C+B) == Q
                assert all(inflate(sig, str(i), 3)[p] == "1"
                           for i in range(3))
            elif a >= 1 and b >= 2:
                s = a+b
                S = b*len(B)+1
                R = S+len(F)
                assert G[S:R] == "10"+B
                assert parikh(G[S:R]) == parikh(F)
                prefix01 = G*b + H + G[:R]
                prefix2 = H+G+F+G*(b-1)+G[:S]
                assert len(prefix01) == len(prefix2) == p
                assert parikh(prefix01) == parikh(prefix2) == Q
                assert all(w[:p] == pref for w, pref in
                           zip(words4, (prefix01, prefix01, prefix2)))
                assert all(w[p] == "1" for w in words4)
            elif a == 0 and b >= 2:
                prefix01 = G*b + H + "1"*b
                prefix2 = H + G + F + G*(b-2) + B*b
                assert len(prefix01) == len(prefix2) == p
                assert parikh(prefix01) == parikh(prefix2) == Q
                assert all(w[:p] == pref for w, pref in
                           zip(words4, (prefix01, prefix01, prefix2)))
                assert all(w[p] == "2" for w in words4)
            else:
                assert (a, b) == (0, 1)
                assert (B, G, H, F) == ("12", "12210", "2101210", "1210")
                assert words4[0][:p] == words4[1][:p] == G + "2101"
                assert words4[2][:p] == H + "12"
                assert parikh(words4[0][:p]) == Q == (2, 4, 3)


def test_complete_literal_swap_diagonal_factors():
    for a in range(6):
        for b in range(6):
            if a + b == 0:
                continue
            sig = family(a, b)
            n, p, _, z = cert(a, b)
            for x, y in combinations("012", 2):
                top = inflate(sig, x+y, n)
                bottom = inflate(sig, y+x, n)
                assert (p, p+1, z, z) in factor(top, bottom)


def test_identical_incidence_and_exact_pisot_integer_conditions():
    def det(m):
        (a,b,c),(d,e,f),(g,h,i) = m
        return a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
    for s in range(1, 13):
        sig = family(0, s) if s <= 8 else family(s-8, 8)
        mat = [[w.count(str(r)) for w in sig] for r in range(3)]
        assert mat == [[1,0,1], [1,s,1], [0,1,1]]
        assert det(mat) == s
        assert all(sum(mat[i][k]*mat[k][j] for k in range(3)) > 0
                   for i in range(3) for j in range(3))
        f = lambda z: z*z*(z-2)-s*(z-1)**2
        for z in (-1,0,1,2,s,max(3,s+1)):
            assert det([[z*(i==j)-mat[i][j] for j in range(3)]
                        for i in range(3)]) == f(z)
        assert f(s) < 0 and f(max(3,s+1)) > 0
        assert -s*(4*s*s-13*s+32) < 0
        assert all(f(z) != 0 for z in range(-s,s+4))


def test_domain_refusals():
    for a, b in ((0,0),(-1,2),(2,-1),(9,1),(1,9),(8,8),(10000,1)):
        try:
            family(a,b)
        except ValueError:
            pass
        else:
            raise AssertionError((a,b))
