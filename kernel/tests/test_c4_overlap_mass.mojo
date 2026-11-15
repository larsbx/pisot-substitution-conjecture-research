"""Exact finite controls for the ordered overlap mass and count interfaces.

The integer fixtures have lengths at most two, images at most three and
residual coordinates in -2..2; every test-local integer operation is bounded
far below Int limits. Production affine prefixes and the production cubic
Perron overlap sweep supply the canonical representations. No new rational
type, overlap graph constructor or geometric loss certificate is introduced.
"""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.affine_ancestry_trace import (
    AffineTraceTables, build_affine_trace_tables, _incidence_action, _prefix_parikh,
)
from psc.hierarchy_offset import prefix_difference3
from psc.renewal import Diff3
from psc.words import Pair
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables, build_seed_overlap_tables
from psc.overlap_zipper import ordered_child_occurrences
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_sub_checked, cubic_mul_beta, sign_at_perron,
)


def _interval_mass(a: Int, b: Int, c: Int, d: Int) -> Int:
    var left = max(a, c)
    var right = min(b, d)
    return max(0, right - left)


def _prefix_mass(word: List[Int], n: Int, lengths: List[Int]) -> Int:
    var out = 0
    for i in range(n):
        out += lengths[word[i]]
    return out


def _offset(r: Diff3, lengths: List[Int]) -> Int:
    return lengths[0] * r.x + lengths[1] * r.y + lengths[2] * r.z


def _mass(a: Int, b: Int, r: Diff3, lengths: List[Int]) -> Int:
    var d = _offset(r, lengths)
    return _interval_mass(0, lengths[a], -d, lengths[b] - d)


def _label(a: Int, b: Int, r: Diff3) -> List[Int]:
    return [a, b, r.x, r.y, r.z]


def _children(tables: AffineTraceTables, a: Int, b: Int, r: Diff3) raises -> List[List[Int]]:
    var out = List[List[Int]]()
    var scaled = _incidence_action(tables, r)
    for i in range(len(tables.sigma[a])):
        var top = _prefix_parikh(tables, a, i)
        for j in range(len(tables.sigma[b])):
            var bottom = _prefix_parikh(tables, b, j)
            out.append([
                i, j, tables.sigma[a][i], tables.sigma[b][j],
                scaled.x + top.x - bottom.x,
                scaled.y + top.y - bottom.y,
                scaled.z + top.z - bottom.z,
            ])
    return out^


def _row_mass(row: List[Int], lengths: List[Int]) -> Int:
    return _mass(row[2], row[3], Diff3(row[4], row[5], row[6]), lengths)


def _row_label(row: List[Int]) -> List[Int]:
    return [row[2], row[3], row[4], row[5], row[6]]


def _sum_mass(rows: List[List[Int]], lengths: List[Int]) -> Int:
    var out = 0
    for i in range(len(rows)):
        out += _row_mass(rows[i], lengths)
    return out


def _scaled(sigma: List[List[Int]], lengths: List[Int], beta: Int) -> Bool:
    if beta < 0:
        return False
    for a in range(3):
        if lengths[a] < 0 or _prefix_mass(sigma[a], len(sigma[a]), lengths) != beta * lengths[a]:
            return False
    return True


def _check_budget(
    tables: AffineTraceTables, a: Int, b: Int, r: Diff3,
    lengths: List[Int], beta: Int,
) raises:
    assert_true(_scaled(tables.sigma, lengths, beta))
    var rows = _children(tables, a, b, r)
    var direct = 0
    for k in range(len(rows)):
        var i = rows[k][0]
        var j = rows[k][1]
        # Independently intersect the actual translated image intervals;
        # this computation does not use the affine residual constructor.
        var top = _prefix_mass(tables.sigma[a], i, lengths)
        var bottom = _prefix_mass(tables.sigma[b], j, lengths) - beta * _offset(r, lengths)
        var cell = _interval_mass(
            top, top + lengths[tables.sigma[a][i]],
            bottom, bottom + lengths[tables.sigma[b][j]],
        )
        assert_equal(_row_mass(rows[k], lengths), cell)
        direct += cell
    assert_equal(_sum_mass(rows, lengths), beta * _mass(a, b, r, lengths))
    assert_equal(direct, beta * _mass(a, b, r, lengths))


def test_finite_binary_scaled_subdivision() raises:
    var checked = 0
    for first in range(4):
        for second in range(4):
            var sigma: List[List[Int]] = [
                [first % 2, (first // 2) % 2],
                [second % 2, (second // 2) % 2], [0, 0],
            ]
            var tables = build_affine_trace_tables(sigma)
            for a in range(2):
                for b in range(2):
                    for x in range(-2, 3):
                        for y in range(-2, 3):
                            _check_budget(tables, a, b, Diff3(x, y, 0), [1, 1, 1], 2)
                            checked += 1
    assert_equal(checked, 1600)


def test_complete_strict_control_is_conservative() raises:
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var lengths: List[Int] = [1, 2, 1]
    var tables = build_affine_trace_tables(sigma)
    var carrier: List[Pair] = [
        Pair([0, 1], [1, 0]), Pair([1, 0], [0, 1]),
        Pair([1, 2], [2, 1]), Pair([2, 1], [1, 2]),
    ]
    var support = List[List[Int]]()
    var checked = 0
    for n in range(len(carrier)):
        var p = carrier[n].copy()
        for i in range(len(p.u)):
            for j in range(len(p.v)):
                var q = prefix_difference3(p.u, p.v, i, j)
                var r = Diff3(q.x, q.y, q.z)
                _check_budget(tables, p.u[i], p.v[j], r, lengths, 2)
                checked += 1
                if _mass(p.u[i], p.v[j], r, lengths) > 0:
                    support.append(_label(p.u[i], p.v[j], r))
    assert_equal(checked, 16)
    assert_equal(len(support), 12)
    for n in range(len(support)):
        var p = support[n].copy()
        var rows = _children(tables, p[0], p[1], Diff3(p[2], p[3], p[4]))
        var retained = 0
        for k in range(len(rows)):
            if _row_mass(rows[k], lengths) == 0:
                continue
            var present = False
            for t in range(len(support)):
                if _row_label(rows[k]) == support[t]:
                    present = True
            assert_true(present)
            retained += _row_mass(rows[k], lengths)
        assert_equal(retained, 2 * _mass(p[0], p[1], Diff3(p[2], p[3], p[4]), lengths))


def test_multiplicity_and_omitted_occurrences() raises:
    var tables = build_affine_trace_tables([[0, 0], [0, 0], [0, 0]])
    var lengths: List[Int] = [1, 1, 1]
    var rows = _children(tables, 0, 1, Diff3(0, 0, 0))
    assert_equal(len(rows), 4)
    assert_equal(_row_label(rows[0]), _row_label(rows[3]))
    assert_equal(rows[0][0], 0)
    assert_equal(rows[3][0], 1)
    var masses = List[Int]()
    var distinct = List[List[Int]]()
    var deduplicated = 0
    for k in range(len(rows)):
        masses.append(_row_mass(rows[k], lengths))
        var label = _row_label(rows[k])
        var seen = False
        for j in range(len(distinct)):
            if label == distinct[j]:
                seen = True
        if not seen:
            distinct.append(label.copy())
            deduplicated += _row_mass(rows[k], lengths)
    assert_equal(masses, [1, 0, 0, 1])
    assert_equal(len(distinct), 3)
    assert_equal(_sum_mass(rows, lengths), 2)
    assert_equal(deduplicated, 1)
    for mask in range(16):
        var retained = 0
        var omitted = 0
        for i in range(4):
            if (mask // (1 << i)) % 2 == 1:
                retained += masses[i]
            else:
                omitted += masses[i]
        assert_equal(2 - retained, omitted)
    # Omitting only the two boundary contacts loses no mass. Omitting an
    # actual positive occurrence creates its exact arithmetic deficit.
    assert_equal(2 - masses[0] - masses[3], 0)
    assert_equal(2 - masses[0], 1)
    assert_equal(_interval_mass(0, 1, 1, 2), 0)
    assert_equal(_interval_mass(0, 0, -1, 1), 0)
    assert_equal(_interval_mass(0, 1, 2, 3), 0)
    assert_true(_scaled([[], [], []], [1, 1, 1], 0))
    assert_true(_scaled([[0], [0], [0]], [0, 0, 0], 2))


def test_wrong_positive_row_and_affine_sign() raises:
    var tables = build_affine_trace_tables([[1], [0, 1, 2], [1]])
    var lengths: List[Int] = [2, 1, 1]
    assert_false(_scaled(tables.sigma, lengths, 2))
    assert_equal(_mass(0, 0, Diff3(0, -1, 0), lengths), 1)
    assert_equal(_sum_mass(_children(tables, 0, 0, Diff3(0, -1, 0)), lengths), 0)
    var rows = _children(tables, 0, 1, Diff3(1, -1, 0))
    assert_equal(rows[1], [0, 1, 1, 1, -2, 0, -1])
    assert_equal(_offset(Diff3(rows[1][4], rows[1][5], rows[1][6]), [1, 2, 1]), -3)


def _field_mass(tables: SeedOverlapTables, p: OverlapState) raises -> CubicElt:
    # SeedOverlap's shift is bottom-minus-top; the Lean packet offset has
    # the opposite sign. This directly uses the native interval convention.
    var left = CubicElt()
    if sign_at_perron(tables.field, p.shift) > 0:
        left = p.shift
    var right = tables.lengths.at(p.top)
    var bottom_end = cubic_add_checked(p.shift, tables.lengths.at(p.bottom))
    if sign_at_perron(tables.field, cubic_sub_checked(bottom_end, right)) < 0:
        right = bottom_end
    var mass = cubic_sub_checked(right, left)
    if sign_at_perron(tables.field, mass) <= 0:
        return CubicElt()
    return mass


def _check_native_sweep(tables: SeedOverlapTables, p: OverlapState) raises -> Int:
    var cells = ordered_child_occurrences(tables, p)
    var total = CubicElt()
    for k in range(len(cells)):
        var mass = cubic_sub_checked(cells[k].right, cells[k].left)
        assert_true(sign_at_perron(tables.field, mass) > 0)
        assert_equal(mass, _field_mass(tables, cells[k].state))
        total = cubic_add_checked(total, mass)
    assert_equal(total, cubic_mul_beta(tables.field, _field_mass(tables, p)))
    return len(cells)


def test_production_perron_sweep_mass() raises:
    var fixtures: List[List[List[Int]]] = [
        [[0, 1], [0, 2], [0]], [[1], [0, 2, 1], [0, 0, 1]],
    ]
    var parents = 0
    var children = 0
    for f in range(len(fixtures)):
        var tables = build_seed_overlap_tables(fixtures[f])
        for a in range(3):
            for b in range(3):
                var p = OverlapState(a, b, CubicElt())
                children += _check_native_sweep(tables, p)
                parents += 1
                var cells = ordered_child_occurrences(tables, p)
                for k in range(len(cells)):
                    children += _check_native_sweep(tables, cells[k].state)
                    parents += 1
    assert_true(parents > 18)
    assert_true(children >= parents)
    print("C4_OVERLAP_MASS_NATIVE_SWEEP", parents, children)


def _count(edges: List[List[Int]], labels: List[Int], x: Int, j: Int, incoming: Bool) -> Int:
    var out = 0
    for k in range(len(edges)):
        if incoming:
            if edges[k][1] == x and labels[edges[k][0]] == j:
                out += 1
        elif edges[k][0] == x and labels[edges[k][1]] == j:
            out += 1
    return out


def _count_matrix(edges: List[List[Int]], labels: List[Int], reps: List[Int], incoming: Bool) -> List[List[Int]]:
    var out = List[List[Int]]()
    for i in range(len(reps)):
        var row = List[Int]()
        for j in range(len(reps)):
            row.append(_count(edges, labels, reps[i], j, incoming))
        out.append(row^)
    return out^


def _fiber_weights(labels: List[Int], reps: List[Int]) -> List[Int]:
    var out = List[Int]()
    for i in range(len(reps)):
        var n = 0
        for x in range(len(labels)):
            if labels[x] == i:
                n += 1
        out.append(n)
    return out^


def _uniform(edges: List[List[Int]], labels: List[Int], reps: List[Int]) -> Bool:
    for x in range(len(labels)):
        for j in range(len(reps)):
            if _count(edges, labels, x, j, False) != _count(edges, labels, reps[labels[x]], j, False):
                return False
            if _count(edges, labels, x, j, True) != _count(edges, labels, reps[labels[x]], j, True):
                return False
    return True


def _weighted(h: List[Int], m: List[Int]) -> List[Int]:
    var out = List[Int]()
    for i in range(len(h)):
        out.append(m[i] * h[i])
    return out^


def _deficit(t: List[List[Int]], h: List[Int], beta: Int, transpose: Bool) -> List[Int]:
    var out = List[Int]()
    for i in range(len(h)):
        var mass = 0
        for j in range(len(h)):
            mass += (t[j][i] if transpose else t[i][j]) * h[j]
        out.append(beta * h[i] - mass)
    return out^


def _check_correspondence(f: List[List[Int]], t: List[List[Int]], m: List[Int]) raises:
    for i in range(len(m)):
        for j in range(len(m)):
            assert_equal(m[i] * t[i][j], m[j] * f[j][i])
    assert_equal(
        _deficit(t, _weighted([1, 2], m), 2, True),
        _weighted(_deficit(f, [1, 2], 2, False), m),
    )


def test_literal_fiber_counts_and_weighted_transpose() raises:
    var labels: List[Int] = [0, 0, 1]
    var reps: List[Int] = [0, 2]
    var edges: List[List[Int]] = [[0, 2], [1, 2], [2, 2]]
    var f = _count_matrix(edges, labels, reps, False)
    var t = _count_matrix(edges, labels, reps, True)
    var m = _fiber_weights(labels, reps)
    assert_true(_uniform(edges, labels, reps))
    assert_equal(m, [2, 1])
    assert_equal(f, [[0, 1], [0, 1]])
    assert_equal(t, [[0, 0], [2, 1]])
    _check_correspondence(f, t, m)
    assert_equal(_deficit(f, [1, 1], 1, False), [0, 0])
    assert_equal(_deficit(t, _weighted([1, 1], m), 1, True), [0, 0])
    assert_equal(_deficit(t, [1, 1], 1, True), [-1, 0])

    # Free/fixed star: the wrong unweighted rule puts strict loss on the
    # wrong quotient vertex, although the exact weighted rule is valid.
    labels = [0, 1, 1]
    reps = [0, 1]
    edges = [[0, 1], [0, 2], [1, 0], [2, 0]]
    f = _count_matrix(edges, labels, reps, False)
    t = _count_matrix(edges, labels, reps, True)
    m = _fiber_weights(labels, reps)
    assert_true(_uniform(edges, labels, reps))
    assert_equal(m, [1, 2])
    assert_equal(f, [[0, 2], [1, 0]])
    assert_equal(t, f)
    _check_correspondence(f, t, m)
    assert_equal(_deficit(f, [1, 1], 2, False), [0, 1])
    assert_equal(_deficit(t, _weighted([1, 1], m), 2, True), [0, 2])
    assert_equal(_deficit(t, [1, 1], 2, True), [1, 0])

    # Every ordered state is fixed, with an actual repeated edge occurrence.
    labels = [0, 1]
    reps = [0, 1]
    edges = [[0, 1], [0, 1], [1, 1]]
    f = _count_matrix(edges, labels, reps, False)
    t = _count_matrix(edges, labels, reps, True)
    m = _fiber_weights(labels, reps)
    assert_equal(m, [1, 1])
    assert_equal(f, [[0, 2], [0, 1]])
    assert_equal(t, [[0, 0], [2, 1]])
    _check_correspondence(f, t, m)

    # Equal free orbit sizes justify the unweighted transpose shortcut.
    labels = [0, 0, 1, 1]
    reps = [0, 2]
    edges = [[0, 2], [1, 3], [2, 2], [3, 3]]
    f = _count_matrix(edges, labels, reps, False)
    t = _count_matrix(edges, labels, reps, True)
    m = _fiber_weights(labels, reps)
    assert_true(_uniform(edges, labels, reps))
    assert_equal(m, [2, 2])
    _check_correspondence(f, t, m)
    for i in range(2):
        for j in range(2):
            assert_equal(f[i][j], t[j][i])
    assert_equal(_deficit([[1, 0], [1, 1]], [2, 2], 2, True), [0, 2])
    assert_equal(_deficit([[1, 0], [1, 1]], [2, 2], 2, False), [2, 0])


def test_finite_quotient_count_domain_and_uniformity() raises:
    var labels: List[Int] = [0, 0, 1]
    var reps: List[Int] = [0, 2]
    var accepted = 0
    for code in range(512):
        var edges = List[List[Int]]()
        for i in range(3):
            for j in range(3):
                if (code // (1 << (3 * i + j))) % 2 == 1:
                    edges.append([i, j])
        if _uniform(edges, labels, reps):
            accepted += 1
            _check_correspondence(
                _count_matrix(edges, labels, reps, False),
                _count_matrix(edges, labels, reps, True),
                _fiber_weights(labels, reps),
            )
    assert_true(accepted > 0)
    assert_true(accepted < 512)
    var nonuniform: List[List[Int]] = [[0, 2]]
    assert_false(_uniform(nonuniform, labels, reps))
    var f = _count_matrix(nonuniform, labels, reps, False)
    var t = _count_matrix(nonuniform, labels, reps, True)
    var m = _fiber_weights(labels, reps)
    assert_true(m[1] * t[1][0] != m[0] * f[0][1])
    print("C4_OVERLAP_MASS_UNIFORM_GRAPHS", accepted, 512)


def main() raises:
    test_finite_binary_scaled_subdivision()
    test_complete_strict_control_is_conservative()
    test_multiplicity_and_omitted_occurrences()
    test_wrong_positive_row_and_affine_sign()
    test_production_perron_sweep_mass()
    test_literal_fiber_counts_and_weighted_transpose()
    test_finite_quotient_count_domain_and_uniformity()
    print("C4 ordered overlap mass and literal quotient-count controls passed.")
    require_contract("all 1600 bounded binary scaled packet budgets and actual strict non-PIP carrier rows conserve occurrence mass; production cubic Perron sweeps conserve exact interval mass; repeated and omitted positive children, zero boundary contact, wrong length scaling, mixed and free orbit weights, transpose orientation and all 512 three-state quotient count inputs preserve the explicit hypothesis boundaries")
