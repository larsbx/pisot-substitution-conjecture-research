"""Literal inverse-digit, interior-ancestry and track-swap quotient controls.

Production incidence/prefix tables and pair canonicalization are reused.
The finite integer fixtures below stay far below Int overflow: binary images
have length two, starting coordinates lie in -2..2, and depth is at most two.
No generic inverse-domain builder or compact-overlap completeness is claimed.
"""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.affine_ancestry_trace import (
    AffineTraceTables, build_affine_trace_tables, _incidence_action, _prefix_parikh,
)
from psc.renewal import Diff3
from psc.hierarchy_offset import prefix_difference3
from psc.words import Pair
from psc.c4_pair_overlap_graph import canonical_pair
from psc.c4_finite_cylinder_overlap import fixture_images, matrix_power
from psc.c4_nonunit_residue_occupancy import inflated_words


def _delta(p: List[Int]) -> Diff3:
    return Diff3(p[2], p[3], p[4])


def _swap(p: List[Int]) -> List[Int]:
    return [p[1], p[0], -p[2], -p[3], -p[4]]


def _canonical(p: List[Int]) -> List[Int]:
    return canonical_pair(p[0], p[1], p[2], p[3], p[4])


def _diagonal(p: List[Int]) -> Bool:
    return p[0] == p[1] and p[2] == 0 and p[3] == 0 and p[4] == 0


def _offset(p: List[Int], lengths: List[Int]) -> Int:
    return lengths[0] * p[2] + lengths[1] * p[3] + lengths[2] * p[4]


def _mass(p: List[Int], lengths: List[Int]) -> Int:
    var d = _offset(p, lengths)
    return max(0, min(lengths[p[0]], lengths[p[1]] - d) - max(0, -d))


def _scaled(sigma: List[List[Int]], lengths: List[Int], beta: Int) -> Bool:
    if beta <= 0:
        return False
    for a in range(3):
        if lengths[a] <= 0:
            return False
        var total = 0
        for j in range(len(sigma[a])):
            total += lengths[sigma[a][j]]
        if total != beta * lengths[a]:
            return False
    return True


def _child(tables: AffineTraceTables, p: List[Int], i: Int, j: Int) raises -> List[Int]:
    var scaled = _incidence_action(tables, _delta(p))
    var top = _prefix_parikh(tables, p[0], i)
    var bottom = _prefix_parikh(tables, p[1], j)
    return [tables.sigma[p[0]][i], tables.sigma[p[1]][j],
        scaled.x + top.x - bottom.x,
        scaled.y + top.y - bottom.y,
        scaled.z + top.z - bottom.z]


def _incoming(tables: AffineTraceTables, p: List[Int], q: List[Int], i: Int, j: Int) raises -> Bool:
    if i < 0 or j < 0 or i >= len(tables.sigma[p[0]]) or j >= len(tables.sigma[p[1]]):
        return False
    if tables.sigma[p[0]][i] != q[0] or tables.sigma[p[1]][j] != q[1]:
        return False
    var top = _prefix_parikh(tables, p[0], i)
    var bottom = _prefix_parikh(tables, p[1], j)
    var scaled = _incidence_action(tables, _delta(p))
    return scaled.x == q[2] + bottom.x - top.x and (
        scaled.y == q[3] + bottom.y - top.y
    ) and scaled.z == q[4] + bottom.z - top.z


def _find(states: List[List[Int]], p: List[Int]) -> Int:
    for i in range(len(states)):
        if states[i] == p:
            return i
    return -1


def _actual_edges(tables: AffineTraceTables, states: List[List[Int]]) raises -> List[List[Int]]:
    var out = List[List[Int]]()
    for n in range(len(states)):
        var p = states[n].copy()
        for i in range(len(tables.sigma[p[0]])):
            for j in range(len(tables.sigma[p[1]])):
                var q = _child(tables, p, i, j)
                var target = _find(states, q)
                if target >= 0:
                    # Distinct i,j identities are retained even if n,target repeat.
                    out.append([n, target, i, j])
    return out^


def _swap_closed(states: List[List[Int]]) -> Bool:
    for i in range(len(states)):
        if _find(states, _swap(states[i])) < 0:
            return False
    return True


def _edge_swap_closed(edges: List[List[Int]], states: List[List[Int]]) -> Bool:
    for k in range(len(edges)):
        var e = edges[k].copy()
        var source = _find(states, _swap(states[e[0]]))
        var target = _find(states, _swap(states[e[1]]))
        if source < 0 or target < 0:
            return False
        var mate: List[Int] = [source, target, e[3], e[2]]
        var count = 0
        for j in range(len(edges)):
            if edges[j] == mate:
                count += 1
        if count != 1:
            return False
    return True


def _representatives(states: List[List[Int]]) -> List[Int]:
    var out = List[Int]()
    for i in range(len(states)):
        if states[i] == _canonical(states[i]):
            out.append(i)
    return out^


def _weight(states: List[List[Int]], representative: Int) -> Int:
    var out = 0
    for i in range(len(states)):
        if _canonical(states[i]) == states[representative]:
            out += 1
    return out


def _count(edges: List[List[Int]], states: List[List[Int]], x: Int, rep: Int, inverse: Bool) -> Int:
    var out = 0
    for k in range(len(edges)):
        var e = edges[k].copy()
        if inverse:
            if e[1] == x and _canonical(states[e[0]]) == states[rep]:
                out += 1
        elif e[0] == x and _canonical(states[e[1]]) == states[rep]:
            out += 1
    return out


def _uniform(edges: List[List[Int]], states: List[List[Int]]) -> Bool:
    var reps = _representatives(states)
    for x in range(len(states)):
        var rep = _find(states, _canonical(states[x]))
        if rep < 0:
            return False
        for j in range(len(reps)):
            if _count(edges, states, x, reps[j], False) != _count(edges, states, rep, reps[j], False):
                return False
            if _count(edges, states, x, reps[j], True) != _count(edges, states, rep, reps[j], True):
                return False
    return True


def _check_counts(edges: List[List[Int]], states: List[List[Int]], free: Bool) raises:
    assert_true(_swap_closed(states))
    assert_true(_edge_swap_closed(edges, states))
    assert_true(_uniform(edges, states))
    var reps = _representatives(states)
    for i in range(len(reps)):
        var wi = _weight(states, reps[i])
        assert_equal(wi, 1 if _diagonal(states[reps[i]]) else 2)
        if free:
            assert_equal(wi, 2)
        for j in range(len(reps)):
            var wj = _weight(states, reps[j])
            var t = _count(edges, states, reps[i], reps[j], True)
            var f = _count(edges, states, reps[j], reps[i], False)
            assert_equal(wi * t, wj * f)
            if free:
                assert_equal(t, f)


def test_binary_inverse_digits_and_ancestry() raises:
    var one_step = 0
    var two_step = 0
    var lengths: List[Int] = [1, 1, 1]
    for first in range(4):
        for second in range(4):
            var sigma: List[List[Int]] = [
                [first % 2, (first // 2) % 2],
                [second % 2, (second // 2) % 2], [0, 0],
            ]
            var tables = build_affine_trace_tables(sigma)
            assert_true(_scaled(sigma, lengths, 2))
            for a in range(2):
                for b in range(2):
                    for x in range(-2, 3):
                        for y in range(-2, 3):
                            var p: List[Int] = [a, b, x, y, 0]
                            assert_equal(_swap(_swap(p)), p)
                            assert_equal(_swap(p) == p, _diagonal(p))
                            for i in range(2):
                                for j in range(2):
                                    var q = _child(tables, p, i, j)
                                    assert_true(_incoming(tables, p, q, i, j))
                                    assert_equal(_child(tables, _swap(p), j, i), _swap(q))
                                    assert_true(_incoming(tables, _swap(p), _swap(q), j, i))
                                    if _mass(q, lengths) > 0:
                                        assert_true(_mass(p, lengths) > 0)
                                        if _diagonal(p):
                                            assert_equal(i, j)
                                            assert_true(_diagonal(q))
                                    one_step += 1
                                    for ii in range(2):
                                        for jj in range(2):
                                            var r = _child(tables, q, ii, jj)
                                            if _mass(r, lengths) > 0:
                                                assert_true(_mass(q, lengths) > 0)
                                                assert_true(_mass(p, lengths) > 0)
                                                if not _diagonal(r):
                                                    assert_false(_diagonal(p))
                                                    assert_false(_diagonal(q))
                                                    assert_true(_swap(p) != p)
                                                    assert_true(_swap(q) != q)
                                            two_step += 1
    assert_equal(one_step, 6400)
    assert_equal(two_step, 25600)
    print("C4_INVERSE_OCCURRENCE_DIGITS", one_step, two_step)


def test_mark_sign_boundary_and_length_guards() raises:
    var tables = build_affine_trace_tables([[1], [0, 1, 2], [1]])
    var p: List[Int] = [0, 1, 1, -1, 0]
    var q = _child(tables, p, 0, 1)
    assert_equal(q, [1, 1, -2, 0, -1])
    assert_true(_incoming(tables, p, q, 0, 1))
    assert_false(_incoming(tables, p, [0, 1, -2, 0, -1], 0, 1))
    assert_false(_incoming(tables, p, q, -1, 1))
    assert_false(_incoming(tables, p, q, 0, 3))
    assert_false(_incoming(tables, p, q, 0, 0))
    # Swapping letters and residual while retaining the wrong digit indices
    # is invalid here: the two source images have different lengths.
    assert_true(_incoming(tables, _swap(p), _swap(q), 1, 0))
    assert_false(_incoming(tables, _swap(p), _swap(q), 0, 1))

    var wrong: List[Int] = [2, 1, 1]
    var correct: List[Int] = [1, 2, 1]
    p = [0, 0, 2, 0, -2]
    q = _child(tables, p, 0, 0)
    assert_false(_scaled(tables.sigma, wrong, 2))
    assert_true(_scaled(tables.sigma, correct, 2))
    assert_equal(_mass(p, wrong), 0)
    assert_equal(_mass(q, wrong), 1)
    assert_equal(_mass(p, correct), 1)
    assert_equal(_mass(q, correct), 2)
    assert_false(_scaled(tables.sigma, correct, 0))

    tables = build_affine_trace_tables([[0, 0], [0, 0], [0, 0]])
    p = [0, 0, 0, 0, 0]
    q = _child(tables, p, 0, 1)
    assert_true(_diagonal(p))
    assert_false(_diagonal(q))
    assert_equal(_mass(q, [1, 1, 1]), 0)
    assert_equal(q, [0, 0, -1, 0, 0])
    # A scalar zero displacement does not make an integral packet fixed.
    p = [0, 0, 1, -1, 0]
    assert_equal(_offset(p, [1, 1, 1]), 0)
    assert_equal(_mass(p, [1, 1, 1]), 1)
    assert_false(_diagonal(p))
    assert_true(_swap(p) != p)


def _strict_states() raises -> List[List[Int]]:
    var pairs: List[Pair] = [
        Pair([0, 1], [1, 0]), Pair([1, 0], [0, 1]),
        Pair([1, 2], [2, 1]), Pair([2, 1], [1, 2]),
    ]
    var out = List[List[Int]]()
    for k in range(len(pairs)):
        for i in range(len(pairs[k].u)):
            for j in range(len(pairs[k].v)):
                var r = prefix_difference3(pairs[k].u, pairs[k].v, i, j)
                var p: List[Int] = [pairs[k].u[i], pairs[k].v[j], r.x, r.y, r.z]
                if _mass(p, [1, 2, 1]) > 0:
                    assert_equal(_find(out, p), -1)
                    out.append(p^)
    return out^


def test_actual_free_orbits_and_induced_subdomains() raises:
    var tables = build_affine_trace_tables([[1], [0, 1, 2], [1]])
    var states = _strict_states()
    assert_equal(len(states), 12)
    var reps = _representatives(states)
    assert_equal(len(reps), 6)
    var edges = _actual_edges(tables, states)
    assert_true(len(edges) > 0)
    _check_counts(edges, states, True)
    for k in range(len(edges)):
        var e = edges[k].copy()
        assert_true(_incoming(tables, states[e[0]], states[e[1]], e[2], e[3]))

    for mask in range(64):
        var subset = List[List[Int]]()
        for x in range(len(states)):
            for j in range(len(reps)):
                if (mask // (1 << j)) % 2 == 1 and _canonical(states[x]) == states[reps[j]]:
                    subset.append(states[x].copy())
        _check_counts(_actual_edges(tables, subset), subset, True)

    var broken = List[List[Int]]()
    for k in range(1, len(edges)):
        broken.append(edges[k].copy())
    assert_equal(len(broken), len(edges) - 1)
    assert_false(_edge_swap_closed(broken, states))
    assert_false(_uniform(broken, states))
    print("C4_INVERSE_OCCURRENCE_FREE_DOMAIN", len(states), len(reps), len(edges), 64)


def test_actual_mixed_orbits_and_parallel_occurrences() raises:
    var tables = build_affine_trace_tables([[0, 0], [0, 0], [0, 0]])
    var states: List[List[Int]] = [[0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]
    var edges = _actual_edges(tables, states)
    assert_equal(len(edges), 6)
    _check_counts(edges, states, False)
    assert_equal(_weight(states, 0), 2)
    assert_equal(_weight(states, 2), 1)
    assert_equal(_count(edges, states, 0, 2, False), 2)
    assert_equal(_count(edges, states, 2, 0, True), 4)
    assert_true(_count(edges, states, 0, 2, False) != _count(edges, states, 2, 0, True))
    assert_equal(edges[0], [0, 2, 0, 0])
    assert_equal(edges[1], [0, 2, 1, 1])
    assert_equal(_child(tables, states[0], 0, 0), _child(tables, states[0], 1, 1))

    var missing: List[List[Int]] = [states[0].copy(), states[2].copy()]
    assert_false(_swap_closed(missing))
    assert_false(_edge_swap_closed(_actual_edges(tables, missing), missing))
    assert_equal(_weight(missing, 0), 1)


def test_inverse_closed_domain_can_leak_forward() raises:
    var tables = build_affine_trace_tables([[0, 0], [1, 1], [2, 2]])
    var states: List[List[Int]] = [[0, 1, 0, 0, 0], [1, 0, 0, 0, 0]]
    var lengths: List[Int] = [1, 1, 1]
    assert_true(_scaled(tables.sigma, lengths, 2))
    var edges = _actual_edges(tables, states)
    assert_equal(len(edges), 2)
    _check_counts(edges, states, True)
    var candidates = 0
    var admitted = 0
    for k in range(len(states)):
        for a in range(3):
            for b in range(3):
                for x in range(-2, 3):
                    for y in range(-2, 3):
                        for z in range(-2, 3):
                            var p: List[Int] = [a, b, x, y, z]
                            for i in range(2):
                                for j in range(2):
                                    if _incoming(tables, p, states[k], i, j):
                                        assert_equal(p, states[k])
                                        assert_equal(i, 0)
                                        assert_equal(j, 0)
                                        admitted += 1
                                    candidates += 1
    assert_equal(candidates, 9000)
    assert_equal(admitted, 2)
    var full_mass = 0
    var retained_mass = 0
    for i in range(2):
        for j in range(2):
            var q = _child(tables, states[0], i, j)
            full_mass += _mass(q, lengths)
            if _find(states, q) >= 0:
                retained_mass += _mass(q, lengths)
    var escaping = _child(tables, states[0], 1, 1)
    assert_equal(escaping, [0, 1, 1, -1, 0])
    assert_equal(_find(states, escaping), -1)
    assert_equal(_mass(escaping, lengths), 1)
    assert_equal(full_mass, 2)
    assert_equal(retained_mass, 1)
    print("C4_INVERSE_OCCURRENCE_FORWARD_LEAK", candidates, admitted, full_mass, retained_mass)


def test_production_nonunit_inverse_arithmetic() raises:
    # Authenticate the same adjugate/divisibility arithmetic as the historical
    # paired-prefix inverse graph, without claiming its boxes or coverage.
    var images = fixture_images(0)
    var words = inflated_words(images, 2)
    var tables = build_affine_trace_tables(words)
    var power = matrix_power(2)
    var inverse_numerator = power.adjugate()
    var determinant = power.det()
    assert_equal(determinant, 4)
    for row in range(3):
        for col in range(3):
            assert_equal(tables.incidence[3 * row + col], power.at(row, col))
    var checked = 0
    var residuals: List[List[Int]] = [[0, 0, 0], [1, -1, 1]]
    for n in range(len(residuals)):
        for a in range(3):
            for b in range(3):
                var p: List[Int] = [a, b, residuals[n][0], residuals[n][1], residuals[n][2]]
                var scaled = _incidence_action(tables, _delta(p))
                assert_equal(power.apply(residuals[n]), [scaled.x, scaled.y, scaled.z])
                for i in range(len(words[a])):
                    for j in range(len(words[b])):
                        var q = _child(tables, p, i, j)
                        var top = _prefix_parikh(tables, a, i)
                        var bottom = _prefix_parikh(tables, b, j)
                        var numerator = inverse_numerator.apply([
                            q[2] + bottom.x - top.x,
                            q[3] + bottom.y - top.y,
                            q[4] + bottom.z - top.z,
                        ])
                        for c in range(3):
                            assert_equal(numerator[c] % determinant, 0)
                            assert_equal(numerator[c] // determinant, p[c + 2])
                        assert_true(_incoming(tables, p, q, i, j))
                        checked += 1
    var rejected = False
    for a in range(3):
        var basis: List[Int] = [0, 0, 0]
        basis[a] = 1
        var numerator = inverse_numerator.apply(basis)
        for c in range(3):
            if numerator[c] % determinant != 0:
                rejected = True
    assert_true(rejected)
    assert_equal(checked, 450)
    print("C4_INVERSE_OCCURRENCE_NONUNIT", checked, determinant)


def main() raises:
    test_binary_inverse_digits_and_ancestry()
    test_mark_sign_boundary_and_length_guards()
    test_actual_free_orbits_and_induced_subdomains()
    test_actual_mixed_orbits_and_parallel_occurrences()
    test_inverse_closed_domain_can_leak_forward()
    test_production_nonunit_inverse_arithmetic()
    print("C4 literal inverse occurrences and track-swap quotient controls passed.")
    require_contract("6400 actual inverse-digit and swapped-index identities, 25600 two-step interior ancestry histories, all 64 swap-closed induced domains of the strict non-PIP fixture, literal free and mixed orbit counts, repeated occurrence identities, boundary/scaling countercontrols, 9000 inverse candidates for the forward-leaking domain and 450 production nonunit adjugate reconstructions preserve the inverse occurrence hypotheses")
