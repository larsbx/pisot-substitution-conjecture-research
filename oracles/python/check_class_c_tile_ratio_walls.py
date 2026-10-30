#!/usr/bin/env python3
"""Independent exact-rational controls for the Class-C tile-ratio chamber proof.

No symbolic cone code, numerical root approximations or third-party packages.
The finite grid tests the *hand-proved* identities rather than replacing proof.
"""
from fractions import Fraction


def chi(n: int, d: int, eps: int, t: Fraction) -> Fraction:
    # Independent expanded cubic, not Mojo's factored characteristic form.
    A = n - d + eps + 3
    B = n - 3 * d + 3 * eps + 2
    return t * t * t - A * t * t + B * t - 2 * eps


def checked() -> None:
    cases = 0
    for eps in (1, -1):
        for d in range(7, 97):
            for c in range(d + 7):
                n = (2 * d - 5 if eps == 1 else 2 * d + 1) + c
                p = n + d
                assert p > 0
                expressions = (
                    (
                        (2*d-1)*c + 6*d*d - 9*d + 4,
                        c*c + 2*c*d - 2*c - 3*d*d - 2*d - 3,
                        2*c*c + 6*c*d + c - 3*d - 10,
                        3*c*c + 10*c*d + 10*c + 3*d*d + 6*d - 13,
                    )
                    if eps == 1 else (
                        (2*d+1)*c + 6*d*d + 9*d + 2,
                        c*c + 2*c*d + 6*c - 3*d*d - 2*d + 9,
                        2*c*c + 6*c*d + 19*c + 15*d + 44,
                    )
                )
                for m, expected in enumerate(expressions, start=1):
                    # Exact rational evaluation, then exact cross multiplication.
                    t = Fraction(2*m + p, m)
                    actual = (m**3) * chi(n, d, eps, t)
                    claimed = p * expected * (1 if m == 1 else -1)
                    assert actual == claimed, (d, eps, c, m, actual, claimed)
                # Sharp independent root test at d+1; the sign locates
                # Delta = ell_x-ell_c = d/(beta-1) against the integer 1.
                at_d_plus_1 = chi(n, d, eps, Fraction(d+1))
                if eps == 1:
                    assert at_d_plus_1 == -d*((d+1)*c-d-3)
                    assert (at_d_plus_1>0) == (c <= 1)
                else:
                    assert at_d_plus_1 == -d*((d+1)*c+3*d+5)
                    assert at_d_plus_1 < 0
                g1, f2, f3 = expressions[:3]
                assert g1 > 0
                if eps == 1:
                    f4 = expressions[3]
                    assert f4 > 0
                    if c == 0:
                        assert f3 < 0
                    elif c <= d+1:
                        assert f3 > 0 and f2 < 0
                    elif c <= d+4:
                        assert f2 > 0
                    if c == 0:
                        assert f3 == -3*d-10
                    if c == 1:
                        assert f3 == 3*d-7
                    if c == d+1:
                        assert f2 == -4
                    if c == d+2:
                        assert f2 == 4*d-3
                elif c <= d-2:
                    assert f2 < 0 and f3 > 0
                    if c == d-2:
                        assert f2 == 1-4*d
                cases += 1
    # Algorithmically separate finite seed-geometry cross-check, using the
    # existing exhaustive-occurrence rational-interval exact oracle. The
    # quantified nine-seed statement is proved by interval inequalities in
    # the note, NOT by these finitely many examples.
    import sys
    from pathlib import Path
    evidence = Path(__file__).resolve().parents[2] / "evidence" / "class-c-residual-domain-2026-10-29"
    sys.path.insert(0, str(evidence))
    from exact_oracle import ExactClassC, ZERO, sub
    finite_seed_members = 0
    for eps in (1, -1):
        for d in (7, 9, 16):
            cs = (0, 1, 2, d-2, d+1, d+4) if eps == 1 else (0, 1, 2, d-2)
            for c in cs:
                n = 2*d + (-5 if eps == 1 else 1) + c
                member = ExactClassC(d, eps, n)
                lengths = member.lengths
                assert member.sign(sub(lengths[0], lengths[1])) > 0
                assert member.sign(sub(lengths[1], lengths[2])) > 0
                expected = set()
                for a in range(3):
                    for b in range(a+1, 3):
                        expected.add((a, b, ZERO))
                        expected.add((a, a, lengths[b]))
                        expected.add((b, a, sub(lengths[b], lengths[a])))
                        assert not member.overlaps((b, b, tuple(-z for z in lengths[a])))
                actual = member.seeds()
                assert len(expected) == len(actual) == 9
                assert set(actual) == expected, (d, eps, n)
                # Bounded, exact, independent observation of the *uniformly
                # hand-proved* 26-child branching bound. Deliberately test
                # every one of the nine seed types at the sharp wall corners.
                if d == 7 and c in (0,1,2):
                    for seed in actual:
                        distinct = set(member.children(seed))
                        assert len(distinct) <= 26, (eps,d,n,seed,len(distinct))
                # Exhaustive ordered-occurrence run/run child generation is
                # algorithmically separate from the integer wall proof.
                # Only assert the two y/y children of the (x,c,0) seed,
                # never a complete or globally closed overlap automaton.
                if d == 7 or (d == 16 and c in (0,1,2)):
                    delta = sub(lengths[0], lengths[1])
                    admissible = (1, 2) if eps == 1 and c <= 1 else (0, 1)
                    expect_yy = {
                        tuple(k * ly - shift for ly, shift in zip(lengths[2], delta))
                        for k in admissible
                    }
                    got_yy = {child[2] for child in member.children((0, 1, ZERO))
                              if child[0] == 2 and child[1] == 2}
                    assert got_yy == expect_yy, (d, eps, n, got_yy, expect_yy)
                    # Exhaustive *all-type* one-step child check of (x,c,0).
                    # These are literal occurrence pairs, not an assumed
                    # symbolic closure or a finite label-set extrapolation.
                    if eps == 1 and c == 0:
                        js, ks, ii = (0, 1), (1, 2), range(n-2, n+3)
                    elif eps == 1 and c == 1:
                        js, ks, ii = (0, 1), (1, 2), range(n-2, n+2)
                    else:
                        js, ks, ii = (0,), (0, 1), range(n-1, n+2)
                    def mul_y(t):
                        return tuple(t*z for z in lengths[2])
                    from exact_oracle import add
                    complete = {(0, 1, ZERO)}
                    complete.update((0, 2, add(lengths[1], mul_y(j))) for j in js)
                    complete.update((2, 2, sub(mul_y(k), delta)) for k in ks)
                    complete.update((2, 0, sub(mul_y(n-i), delta)) for i in ii)
                    all_children = set(member.children((0, 1, ZERO)))
                    assert all_children == complete, (d, eps, n, all_children - complete, complete - all_children)
                    assert len(complete) == (10 if eps==1 and c==0 else 9 if eps==1 and c==1 else 7)
                    # Second fully classified aligned seed (c,y,0):
                    # first/first, run/run and every actual run/last match.
                    if eps == 1 and c == 0:
                        last_indices = (0, -1, -2)
                    else:
                        last_indices = (0, -1)
                    cy_children = {(1, 1, ZERO), (2, 2, ZERO)}
                    cy_children.update((2, 1, mul_y(k)) for k in last_indices)
                    got_cy = set(member.children((1, 2, ZERO)))
                    assert got_cy == cy_children, (d, eps, n, got_cy - cy_children, cy_children - got_cy)
                    assert len(cy_children) == (5 if eps == 1 and c == 0 else 4)
                    # Algebraically exact cross-tile identity, using the
                    # cubic companion action, independent of sign bracketing:
                    # beta*(2*Lc-Lx-Ly)+eps*Ly == 0.
                    q = sub(sub(tuple(2*z for z in lengths[1]), lengths[0]), lengths[2])
                    assert add(member.beta(q), tuple(eps*z for z in lengths[2])) == ZERO
                    # Third aligned seed (x,y,0), including every actual
                    # first/run, run/run, and run/last occurrence pair.
                    J, K = ((0,1),(1,2)) if eps==1 and c<=1 else ((0,),(0,1))
                    r = n-d+eps
                    if eps==1 and c<=1:
                        I = range(r-2,r+1)
                    elif eps==1:
                        I = range(r-1,r+1)
                    else:
                        I = range(r-1,r+2)
                    xy_children = {(0,1,ZERO)}
                    xy_children.update((0,2,add(lengths[1],mul_y(j))) for j in J)
                    xy_children.update((2,2,sub(mul_y(k),delta)) for k in K)
                    xy_children.update((2,1,sub(mul_y(r-i),delta)) for i in I)
                    got_xy = set(member.children((0,2,ZERO)))
                    assert got_xy == xy_children, (d,eps,n,got_xy-xy_children,xy_children-got_xy)
                    assert len(xy_children) == (8 if eps==1 and c<=1 else 6 if eps==1 else 7)
                finite_seed_members += 1
    print("TILE_RATIO_EXACT_RATIONAL_ORACLE_PASS", cases)
    print("CANONICAL_NINE_SEEDS_FINITE_PASS", finite_seed_members)


if __name__ == "__main__":
    checked()
