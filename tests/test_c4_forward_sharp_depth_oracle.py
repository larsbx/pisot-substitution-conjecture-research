"""Independent exact-word oracle for sharp simultaneous *forward* family depths.

The symbolic (unbounded-parameter) lower-bound proof is in
docs/c4-forward-run-family-sharp-depth-2026-11-04.md.
This finite independent replay checks *all* earlier-level candidate cuts,
not only the displayed positive witnesses, but is not a proof of infinity.
"""
from itertools import combinations


def family(a, b):
    if a < 0 or b < 0 or a + b == 0 or a > 16 or b > 16:
        raise ValueError("singular, negative or over oracle budget")
    return ("01", "1" * a + "2" + "1" * b, "012")


def inflate(sig, initial, level):
    word = initial
    for _ in range(level):
        word = "".join(sig[int(c)] for c in word)
    return word


def prefix_mass(w):
    count = [0, 0, 0]
    yield (0, 0, 0)
    for c in w:
        count[int(c)] += 1
        yield tuple(count)


def all_simultaneous_cuts(sig, level):
    words = [inflate(sig, str(i), level) for i in range(3)]
    masses = [list(prefix_mass(w)) for w in words]
    return [
        (p, masses[0][p], words[0][p])
        for p in range(min(map(len, words)))
        if masses[0][p] == masses[1][p] == masses[2][p]
        and words[0][p] == words[1][p] == words[2][p]
    ]


def sharp_certificate(a, b):
    family(a, b)  # validate separately from the formulas
    s = a + b
    if a == 0:
        return 2, 0, (0, 0, 0), "0"
    if a == 1 and b == 0:
        return 3, 7, (2, 3, 2), "1"
    if a == 1:
        return 2, s + 2, (1, s, 1), "1"
    if b == 0:
        return 4, a**3 + a*a + 4*a + 1, (a+1, a**3+2*a, a*(a+1)), "1"
    return 3, a*(s+1)+1, (1, a*s, a), "1"


def complete_factors(u, v):
    assert sorted(u) == sorted(v)
    diff = [0, 0, 0]
    start = 0
    factors = []
    for i, (x, y) in enumerate(zip(u, v), 1):
        diff[int(x)] += 1
        diff[int(y)] -= 1
        if diff == [0, 0, 0]:
            factors.append((start, i, u[start:i], v[start:i]))
            start = i
    assert start == len(u) == len(v)
    return factors


def test_complete_sharp_certificate_and_exhaust_all_smaller_levels():
    for a in range(10):
        for b in range(10):
            if a + b == 0:
                continue
            sigma = family(a, b)
            n, p, Q, z = sharp_certificate(a, b)
            assert (p, Q, z) in all_simultaneous_cuts(sigma, n), (a, b)
            for earlier in range(1, n):
                assert not all_simultaneous_cuts(sigma, earlier), (a, b, earlier)


def test_literal_new_level_two_identity_for_a_one_positive_right():
    for b in range(1, 16):
        sigma = family(1, b)
        A, B, C = sigma
        F = A + B
        G = B + C + B * b
        H = F + C
        p = b + 3
        prefix0 = "0112" + "1" * (b - 1)
        prefix1 = B + "0"
        assert len(prefix0) == len(prefix1) == p
        assert (F, G, H) == tuple(inflate(sigma, str(i), 2) for i in range(3))
        assert F[:p] == H[:p] == prefix0 and G[:p] == prefix1
        assert F[p] == G[p] == H[p] == "1"
        assert tuple(prefix0.count(str(i)) for i in range(3)) == (1, b+1, 1)
        assert tuple(prefix1.count(str(i)) for i in range(3)) == (1, b+1, 1)


def test_literal_exception_a_one_b_zero_depth_three():
    sigma = family(1, 0)
    A, B, C = sigma
    F, G, H = A+B, B+C, A+B+C
    assert (F,G,H) == ("0112", "12012", "0112012")
    assert [inflate(sigma,str(i),3) for i in range(3)] == [
        F+G, G+H, F+G+H,
    ]
    assert (F+G)[:7] == (F+G+H)[:7] == "0112120"
    assert (G+H)[:7] == "1201201"
    assert all(w[7] == "1" for w in (F+G,G+H,F+G+H))
    assert all(tuple(w[:7].count(str(i)) for i in range(3)) == (2,3,2)
               for w in (F+G,G+H,F+G+H))


def test_right_boundary_third_level_all_balanced_cuts_have_wrong_letters():
    # Paper proof: for a>=2, sigma^3(0)=FG, sigma^3(1)=G^a H;
    # the complete list of equally abelianized prefixes (within FG) is
    # p=0, a(a+1)+2, a(a+1)+a+3; all have unequal next letters.
    for a in range(2, 13):
        sig = family(a, 0)
        w0,w1,w2 = [inflate(sig,str(i),3) for i in range(3)]
        K = a*(a+1)
        P = K+a+3
        first, second = list(prefix_mass(w0)), list(prefix_mass(w1))
        positions = [p for p in range(len(w0))
                     if first[p] == second[p]]
        assert positions == [0, K+2, P], (a, positions)
        assert [(w0[p],w1[p]) for p in positions] == [
            ("0","1"), ("1","2"), ("0","2"),
        ]
        assert w2.startswith(w0)


def test_real_complete_swap_factorization_at_sharp_level():
    for a in range(7):
        for b in range(7):
            if a+b == 0:
                continue
            sigma = family(a,b)
            n,p,_,z = sharp_certificate(a,b)
            for x,y in combinations("012",2):
                top = inflate(sigma,x+y,n)
                bottom = inflate(sigma,y+x,n)
                assert (p,p+1,z,z) in complete_factors(top,bottom), (a,b,x,y)


def test_fixed_incidence_does_not_fix_even_the_minimum_level():
    for s in (2,3,4,5,6):
        cuts = [sharp_certificate(a,s-a)[:2] for a in range(s+1)]
        assert cuts[0][0] == 2 and cuts[1][0] == 2
        assert all(n == 3 for n,p in cuts[2:-1])
        assert cuts[-1][0] == 4
        assert all(family(a,s-a)[1].count("1") == s
                   for a in range(s+1))


def test_invalid_parameter_budget_refuses():
    for a,b in ((0,0),(-1,1),(1,-1),(17,0),(0,17),(999,0)):
        try:
            sharp_certificate(a,b)
        except ValueError:
            pass
        else:
            raise AssertionError((a,b))


def pair_cuts(words, i, j):
    """Independent direct pairwise cut enumeration, including all alternatives."""
    u, v = words[i], words[j]
    pu, pv = list(prefix_mass(u)), list(prefix_mass(v))
    return [(p, pu[p], u[p]) for p in range(min(len(u), len(v)))
            if pu[p] == pv[p] and u[p] == v[p]]


def test_prefix_satellite_word_identity_and_exact_cut_set_equivalence():
    # This is a word-level identity, not merely incidence compatibility.
    for a in range(7):
        for b in range(7):
            if a+b == 0:
                continue
            sigma = family(a,b)
            for level in range(1,5):
                words = [inflate(sigma,str(c),level) for c in range(3)]
                assert words[2] == words[0] + inflate(sigma, "2", level-1)
                assert pair_cuts(words,0,1) == all_simultaneous_cuts(sigma,level)


def test_sharp_pairwise_minima_in_all_five_chambers():
    for a in range(10):
        for b in range(10):
            if a+b==0:
                continue
            sigma = family(a,b)
            n,p,Q,z = sharp_certificate(a,b)
            pairwise = {}
            for depth in range(1,n+1):
                words = [inflate(sigma,str(c),depth) for c in range(3)]
                for i,j in combinations(range(3),2):
                    cuts = pair_cuts(words,i,j)
                    if cuts and (i,j) not in pairwise:
                        pairwise[i,j] = depth
            assert pairwise == {(0,1):n,(0,2):1,(1,2):n}, (a,b,pairwise)
            assert (p,Q,z) in pair_cuts(words,0,1)
            assert (p,Q,z) in pair_cuts(words,1,2)


def test_incidence_only_cannot_replace_literal_prefix_satellite():
    # 2-images have equal letter counts in both systems, but the broken
    # system does not have sigma(2)=sigma(0) + a suffix AS A WORD.
    good=("10","1","100")
    bad =("10","1","010")
    assert all(sorted(good[i]) == sorted(bad[i]) for i in range(3))
    assert good[2] == good[0] + "0"
    assert bad[2] != bad[0] + "0"
    good_words=list(good)
    bad_words=list(bad)
    assert (0,(0,0,0),"1") in pair_cuts(good_words,0,1)
    assert (0,(0,0,0),"1") in pair_cuts(bad_words,0,1)
    assert (0,(0,0,0),"1") in all_simultaneous_cuts(good,1)
    assert (0,(0,0,0),"1") not in all_simultaneous_cuts(bad,1)


def test_right_zero_pair_12_third_level_all_balanced_positions():
    for a in range(2,13):
        sig=family(a,0)
        y=inflate(sig,"1",3)
        z=inflate(sig,"2",3)
        m1,m2=list(prefix_mass(y)),list(prefix_mass(z))
        positions=[p for p in range(min(len(y),len(z)))
                   if m1[p]==m2[p]]
        K=a*(a+1)
        P=K+a+3
        assert positions==[0,K+2,P],(a,positions)
        assert [(y[p],z[p]) for p in positions]==[
            ("1","0"),("2","1"),("2","0")],(a,positions)
