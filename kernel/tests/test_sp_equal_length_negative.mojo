"""Exact negative controls from the PSC v5-thread salvage audit (PR #331).

Pins `docs/psc-v5-thread-salvage-audit-2026-10-23.md` §§B–C on the PIP
substitution `0 -> 12, 1 -> 01, 2 -> 120` (det -1):

- `120 = 12 . 0` makes `u = 0` a reachable initial residual;
- `0 . 12 = 01 . 2` is a same-orientation edge `u = 0 -> v = 2` with
  `|u| = |v|`, `u != v` and source letters `0 != 1`, so "equal-length
  preserved-orientation SP edges are identities" is false on PIP;
- Sardinas–Patterson still certifies the image code uniquely decipherable,
  so the edge is no route to a non-UD return (UD stands by the defect theorem);
- the residual-length cycle `1 -> 2 -> 1` has no equal-length edge, refuting
  "a minimum-length vertex on a cycle gives an equal-length subcycle";
- the equal-length code `{01, 12, 20}` (det 2) parses `(012)^infty` at three
  distinct phases: finite-word UD does not fix bi-infinite cut positions.

The Python oracle `tests/test_sp_equal_length_negative.py` checks the same
facts independently.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.bpa import substitution_incidence
from psc.pisot import is_pip


def sigma_of(a: List[Int], b: List[Int], c: List[Int]) -> List[List[Int]]:
    var sigma = List[List[Int]]()
    sigma.append(a.copy())
    sigma.append(b.copy())
    sigma.append(c.copy())
    return sigma^


def fixture() -> List[List[Int]]:
    return sigma_of([1, 2], [0, 1], [1, 2, 0])


def concat(x: List[Int], y: List[Int]) -> List[Int]:
    var w = x.copy()
    for i in range(len(y)):
        w.append(y[i])
    return w^


def same(x: List[Int], y: List[Int]) -> Bool:
    if len(x) != len(y):
        return False
    for i in range(len(x)):
        if x[i] != y[i]:
            return False
    return True


def is_prefix(p: List[Int], w: List[Int]) -> Bool:
    if len(p) > len(w):
        return False
    for i in range(len(p)):
        if p[i] != w[i]:
            return False
    return True


def suffix_after(p: List[Int], w: List[Int]) -> List[Int]:
    """`w = p . s`; returns `s` (caller checks `is_prefix(p, w)`)."""
    var s = List[Int]()
    for i in range(len(p), len(w)):
        s.append(w[i])
    return s^


def contains(ws: List[List[Int]], w: List[Int]) -> Bool:
    for i in range(len(ws)):
        if same(ws[i], w):
            return True
    return False


def sardinas_patterson_ud(code: List[List[Int]]) -> Bool:
    """Classical Sardinas–Patterson test: no dangling suffix is empty or a codeword."""
    var frontier = List[List[Int]]()
    for i in range(len(code)):
        for j in range(len(code)):
            if i != j and is_prefix(code[i], code[j]):
                var s = suffix_after(code[i], code[j])
                if not contains(frontier, s):
                    frontier.append(s^)
    var seen = List[List[Int]]()
    while len(frontier) > 0:
        var s = frontier.pop()
        if len(s) == 0 or contains(code, s):
            return False
        if contains(seen, s):
            continue
        seen.append(s.copy())
        for k in range(len(code)):
            if is_prefix(code[k], s):
                frontier.append(suffix_after(code[k], s))
            elif is_prefix(s, code[k]):
                frontier.append(suffix_after(s, code[k]))
    return True


def test_fixture_is_pip() raises:
    var m = Mat3(substitution_incidence(fixture()))
    assert_equal(m.det(), -1)
    assert_true(is_pip(m))


def test_initial_residual_is_reachable() raises:
    var s = fixture()
    var u: List[Int] = [0]
    assert_true(same(s[2], concat(s[0], u)))


def test_equal_length_nonidentity_edge() raises:
    """`u . sigma(0) = sigma(1) . v` with `u = 0`, `v = 2`."""
    var s = fixture()
    var u: List[Int] = [0]
    var top = concat(u, s[0])
    assert_true(is_prefix(s[1], top))
    var v = suffix_after(s[1], top)
    assert_equal(len(v), len(u))
    assert_false(same(u, v))
    assert_true(same(v, [2]))


def test_fixture_code_is_still_ud() raises:
    assert_true(sardinas_patterson_ud(fixture()))
    # Control: the oracle does refuse a non-code (`0 . 01 = 00 . 1`).
    var bad = List[List[Int]]()
    bad.append([0])
    bad.append([0, 1])
    bad.append([1])
    assert_false(sardinas_patterson_ud(bad))


def test_minimum_does_not_force_equal_length_edge() raises:
    var lengths: List[Int] = [1, 2]
    for i in range(len(lengths)):
        assert_true(lengths[i] != lengths[(i + 1) % len(lengths)])


def test_uniform_code_has_three_bi_infinite_phases() raises:
    var code = sigma_of([0, 1], [1, 2], [2, 0])
    assert_equal(Mat3(substitution_incidence(code)).det(), 2)
    assert_true(sardinas_patterson_ud(code))
    var parsing_phases = 0
    for phase in range(3):
        var ok = True
        for block in range(3):
            var w: List[Int] = [(phase + 2 * block) % 3, (phase + 2 * block + 1) % 3]
            ok = ok and contains(code, w)
        if ok:
            parsing_phases += 1
    assert_equal(parsing_phases, 3)


def main() raises:
    test_fixture_is_pip()
    test_initial_residual_is_reachable()
    test_equal_length_nonidentity_edge()
    test_fixture_code_is_still_ud()
    test_minimum_does_not_force_equal_length_edge()
    test_uniform_code_has_three_bi_infinite_phases()
    require_contract("PSC v5-thread SP negative controls: equal-length nonidentity PIP edge with UD intact")
