"""Independent oracle for `kernel/tests/test_sp_equal_length_negative.mojo`.

Pins the exact PR #331 negative controls of
`docs/psc-v5-thread-salvage-audit-2026-10-23.md` §§B–C with integer and
string arithmetic only.
"""

from fractions import Fraction
from itertools import product

SIGMA = ("12", "01", "120")


def incidence(sigma):
    return [[w.count(str(i)) for w in sigma] for i in range(3)]


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def det(m):
    return (
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
        - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
        + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    )


def charpoly(m):
    """Coefficients of x^3 + c2 x^2 + c1 x + c0, as (c2, c1, c0)."""
    m2 = matmul(m, m)
    tr, tr2 = sum(m[i][i] for i in range(3)), sum(m2[i][i] for i in range(3))
    return -tr, (tr * tr - tr2) // 2, -det(m)


def sardinas_patterson_ud(code):
    dangling = {b[len(a):] for a, b in product(code, repeat=2) if a != b and b.startswith(a)}
    seen = set()
    while dangling - seen:
        s = (dangling - seen).pop()
        if s == "" or s in code:
            return False
        seen.add(s)
        dangling |= {s[len(c):] for c in code if s.startswith(c)}
        dangling |= {c[len(s):] for c in code if c.startswith(s)}
    return True


def test_fixture_is_primitive_irreducible_pisot():
    m = incidence(SIGMA)
    assert m == [[0, 1, 1], [1, 1, 1], [1, 0, 1]]
    assert det(m) == -1
    c2, c1, c0 = charpoly(m)
    assert (c2, c1, c0) == (-2, -1, 1)
    chi = lambda x: x**3 + c2 * x**2 + c1 * x + c0
    assert all(chi(r) != 0 for r in (1, -1))  # monic cubic, no rational root
    assert all(v > 0 for row in matmul(matmul(m, m), m) for v in row)
    # Pisot, by exact sign changes: one root in (2, 3), two in (-1, 1).
    q = Fraction
    assert chi(2) < 0 < chi(3)
    assert chi(0) > 0 > chi(q(9, 10)) and chi(-1) < 0 < chi(q(-1, 2))


def test_reachable_residual_and_equal_length_nonidentity_edge():
    assert SIGMA[2] == SIGMA[0] + "0"
    u, top = "0", "0" + SIGMA[0]
    assert top.startswith(SIGMA[1])
    v = top[len(SIGMA[1]):]
    assert (len(u), u != v, v) == (len(v), True, "2")


def test_ud_holds_and_oracle_refuses_a_non_code():
    assert sardinas_patterson_ud(SIGMA)
    assert not sardinas_patterson_ud(("0", "01", "1"))


def test_uniform_code_has_two_bi_infinite_parsings():
    """Cut sets c + 2Z, c in {0, 1}; one period lcm(2, 3) = 6 decides each."""
    code = ("01", "12", "20")
    assert det(incidence(code)) == 2 and sardinas_patterson_ud(code)
    word = "012" * 4
    parsings = [c for c in range(2) if all(word[c + 2 * k : c + 2 * k + 2] in code for k in range(3))]
    assert parsings == [0, 1]


if __name__ == "__main__":
    for name, fn in list(globals().items()):
        if name.startswith("test_"):
            fn()
    print("ok")
