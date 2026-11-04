"""Independent literal Python cut-pair oracle (bounded, no C4/PDS claim).

This is intentionally not an implementation of Rauzy-subtile volume.
It checks only the combinatorial Theorem-A necessary conditions:
actual zero-return cuts, true source first-pair mask, full child closure,
and bounded common-letter/equal-Parikh-prefix witnesses.
"""
from collections import Counter
from itertools import combinations


def inflate(sigma, word):
    return "".join(sigma[int(x)] for x in word)


def cuts(u, v):
    if Counter(u) != Counter(v) or not u:
        raise ValueError("not a nonempty balanced pair")
    if len(u) != len(v):
        raise ValueError("unequal source length")
    a, b = Counter(), Counter()
    out = [0]
    for i, (x, y) in enumerate(zip(u, v), 1):
        a[x] += 1
        b[y] += 1
        if a == b:
            out.append(i)
            a.clear()
            b.clear()
    if out[-1] != len(u):
        raise ValueError("terminal balanced return missing")
    return out


def factors(u, v):
    bs = cuts(u, v)
    return [(u[bs[j]:bs[j + 1]], v[bs[j]:bs[j + 1]])
            for j in range(len(bs) - 1)]


def pair(u, v):
    if u == v:
        raise ValueError("diagonal cannot be a strict cut pair")
    return frozenset((u, v))


def bounded_strong_coincidence(sigma, a, b, cap):
    if cap < 1 or cap > 10:
        raise ValueError("invalid witness cap")
    u, v = str(a), str(b)
    for depth in range(1, cap + 1):
        u, v = inflate(sigma, u), inflate(sigma, v)
        ca, cb = Counter(), Counter()
        for x, y in zip(u, v):
            if ca == cb and x == y:
                return depth
            ca[x] += 1
            cb[y] += 1
    return None  # finite budget exhausted, NOT a noncoincidence theorem


def strict_complete_system(sigma, states):
    """Check ORDERED strict child closure (no track-swap normalisation)."""
    ordered = set(states)
    if len(ordered) != len(states) or len({frozenset(s) for s in states}) != len(states):
        raise ValueError("duplicate state or orientation pair")
    A = set()
    ordered_children = []
    for u, v in states:
        assert cuts(u, v) == [0, len(u)]
        A.add(pair(u[0], v[0]))
        child = factors(inflate(sigma, u), inflate(sigma, v))
        if any(x == y or (x, y) not in ordered for x, y in child):
            raise ValueError("not a complete strict child-closed system")
        ordered_children.append(child)
    first = {str(i): sigma[i][0] for i in range(3)}
    for edge in A:
        a, b = sorted(edge)
        assert first[a] != first[b]
        assert pair(first[a], first[b]) in A
    return A, ordered_children


def test_reducible_fullrank_strict_actual_cut_pairs_are_one_type():
    sigma = ("10", "102", "211")
    states = (
        ("102", "210"),
        ("11102", "21110"),
        ("10210211", "21110210"),
        ("10210210210211", "21110210210210"),
    )
    A, children = strict_complete_system(sigma, states)
    assert A == {frozenset(("1", "2"))}
    assert [len(row) for row in children] == [1, 1, 5, 9]
    assert bounded_strong_coincidence(sigma, 0, 1, 8) == 1
    assert bounded_strong_coincidence(sigma, 1, 2, 8) is None


def test_constant_length_nonpisot_has_all_three_cut_pairs():
    sigma = ("012", "120", "201")
    # The earlier listing is closed only up to track swap: (201,012) is a
    # child and is missing. Ordered closure must refuse it.
    swapped = ((sigma[0], sigma[1]), (sigma[0], sigma[2]), (sigma[1], sigma[2]))
    try:
        strict_complete_system(sigma, swapped)
    except ValueError:
        pass
    else:
        raise AssertionError("track-swap-only closure was accepted as ordered")
    states = ((sigma[0], sigma[1]), (sigma[1], sigma[2]), (sigma[2], sigma[0]))
    A, children = strict_complete_system(sigma, states)
    assert A == {frozenset((str(a), str(b)))
                 for a, b in combinations(range(3), 2)}
    assert all(len(row) > 0 for row in children)
    assert all(bounded_strong_coincidence(sigma, a, b, 6) is None
               for a, b in combinations(range(3), 2))


def test_pisot_pairwise_strong_coincidence_is_a_real_prefix_witness():
    sigma = ("01", "121", "012")
    assert all(bounded_strong_coincidence(sigma, a, b, 2) is not None
               for a, b in combinations(range(3), 2))
    for a, b in combinations(range(3), 2):
        u, v = str(a)+str(b), str(b)+str(a)
        for _ in range(2):
            u, v = inflate(sigma, u), inflate(sigma, v)
        assert any(x == y for x, y in factors(u, v))
    # The bounded scanner must never silently return an absence verdict
    # for malformed or zero/over-limit budgets.
    for n in (-1, 0, 11):
        try:
            bounded_strong_coincidence(sigma, 0, 1, n)
        except ValueError:
            pass
        else:
            raise AssertionError("bad search budget was accepted")


def test_transient_pair_six_state_strict_closure():
    sigma = ("10", "102", "211")
    states = (
        ("02", "20"), ("10211", "21110"), ("102", "210"), ("11102", "21110"),
        ("10210211", "21110210"), ("10210210210211", "21110210210210"),
    )
    A, _ = strict_complete_system(sigma, states)
    assert A == {frozenset("02"), frozenset("12")}
    assert bounded_strong_coincidence(sigma, 0, 2, 8) is None


def test_unit_pip_left_witness_levels():
    sigma = ("01", "12", "021")
    assert bounded_strong_coincidence(sigma, 0, 2, 8) == 1
    assert bounded_strong_coincidence(sigma, 0, 1, 8) == 4
    assert bounded_strong_coincidence(sigma, 1, 2, 8) == 4
