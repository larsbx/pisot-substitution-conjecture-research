"""Literal prefix refutations of the twin marker law on the even C4 residue.

This checks every singleton corner with all four grouped cells, including
any corner which the grouped-cycle argument might already exclude. It uses
original periodic right rays and makes no assumption on computing stacks.
"""

from std.testing import assert_equal
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution
from psc.c4_geometric_f import chi_mod2_code, principal_minor_sum
from psc.corpus import pip_corpus
from psc.h1_census import eventual_range, h1_profile, legal_two_words
from psc.histogram import Histogram

comptime ENDPOINT_POWER = 6
comptime RAY_POWER = 12
comptime WORD_CAP = 531441  # 3^12 in the standing short-image corpus


def periodic_endpoints(sigma: List[List[Int]], first: Bool) -> List[Int]:
    var result = List[Int]()
    for a in range(3):
        var end = a
        for _ in range(ENDPOINT_POWER):
            end = sigma[end][0 if first else len(sigma[end]) - 1]
        result.append(end)
    return result^


def has_grouped_square(er: List[Bool], a0: Int, b0: Int) -> Bool:
    var cells = List[Bool](length=4, fill=False)
    for a in range(3):
        for b in range(3):
            if er[3 * a + b]:
                cells[2 * Int(a != a0) + Int(b != b0)] = True
    return cells[0] and cells[1] and cells[2] and cells[3]


def periodic_right_rays(sigma: List[List[Int]]) raises -> List[List[Int]]:
    var rays = List[List[Int]]()
    for b in range(3):
        var ray: List[Int] = [b]
        for _ in range(RAY_POWER):
            if 3 * len(ray) > WORD_CAP:
                raise Error("literal right ray exceeds the replay cap")
            ray = apply_substitution(sigma, ray)
        rays.append(ray^)
    return rays^


def marker_violation(
    top: List[Int], bottom: List[Int], last: List[Int], first: List[Int], a0: Int, b0: Int
) -> Int:
    """First prefix length violating the law, or zero if the replay has none.

    The starting seams have opposite groups by construction. Keep both
    projected endpoint flips at the terminal cut so a hit specifically
    refutes the marker parity. All tests are in original word coordinates.
    """
    var balance = List[Int](length=3, fill=0)
    var marks = 0
    for i in range(min(len(top), len(bottom)) - 1):
        var a = top[i]
        var b = bottom[i]
        balance[a] += 1
        balance[b] -= 1
        if i > 0:
            marks += Int(last[top[i - 1]] == a0 and first[a] == b0)
            marks -= Int(last[bottom[i - 1]] == a0 and first[b] == b0)
        if balance[0] != 0 or balance[1] != 0 or balance[2] != 0:
            continue
        var last_bit = last[a] != a0
        if last_bit == (last[b] != a0):
            continue
        if (first[top[i + 1]] == b0) == (first[bottom[i + 1]] == b0):
            continue
        var required = 1 + Int(first[top[0]] != b0) + Int(last_bit)
        if (marks - required) % 2 != 0:
            return i + 1
    return 0


def main() raises:
    var corpus = pip_corpus()
    assert_equal(len(corpus), 4554)
    var eligible = 0
    var refuted = 0
    var longest = 0
    var shapes = Histogram(400)
    for specimen in corpus:
        ref m = specimen.incidence
        if chi_mod2_code(m.det(), m.trace(), principal_minor_sum(m)) != 0:
            continue
        var h = h1_profile(specimen.sigma)
        if h.dimension <= 3:
            continue
        eligible += 1
        assert_equal(h.components, 1)
        var er = eventual_range(specimen.sigma, legal_two_words(specimen.sigma))
        var left = 0
        var right = 0
        for a in range(3):
            var row = False
            var column = False
            for b in range(3):
                row = row or er[3 * a + b]
                column = column or er[3 * b + a]
            left += Int(row)
            right += Int(column)
        var shape = 100 * left + 10 * right + h.edges
        var last = periodic_endpoints(specimen.sigma, False)
        var first = periodic_endpoints(specimen.sigma, True)
        var rays = periodic_right_rays(specimen.sigma)
        var markers = 0
        for a0 in range(3):
            for b0 in range(3):
                if not er[3 * a0 + b0] or not has_grouped_square(er, a0, b0):
                    continue
                markers += 1
                assert_equal(last[a0], a0)
                assert_equal(first[b0], b0)
                var witness = 0
                for b1 in range(3):
                    if b1 == b0:
                        continue
                    var opposite_seam = False
                    for a1 in range(3):
                        opposite_seam = opposite_seam or (a1 != a0 and er[3 * a1 + b1])
                    if not opposite_seam:
                        continue
                    assert_equal(first[b1], b1)
                    witness = marker_violation(rays[b0], rays[b1], last, first, a0, b0)
                    if witness > 0:
                        break
                if witness == 0:
                    raise Error("no right-prefix marker witness for " + specimen.label() +
                        " at seam " + String(a0) + "." + String(b0))
                refuted += 1
                longest = max(longest, witness)
                shapes.record(shape)
        if markers == 0:
            raise Error("no grouped square on retained specimen " + specimen.label())
    assert_equal(eligible, 96)
    assert_equal(refuted, 540)
    assert_equal(longest, 5038)
    assert_equal(shapes.line("marker witnesses"),
                 "marker witnesses 224:96 235:24 236:144 325:24 326:144 339:108")
    print("even residue", eligible, "singleton markers", refuted, "max prefix", longest)
    print(shapes.line("marker witnesses"))
    require_contract("The original alphabet marker parity law has a positive literal right-prefix refutation at every one of the 540 singleton markers with four grouped cells across the 96 nilpotent positive-cycle corpus specimens. The two prefixes have equal Parikh counts and opposite projected endpoint groups at the terminal cut. The replay uses power 12 and a 531441-letter cap, with maximum witness prefix length 5038.")
