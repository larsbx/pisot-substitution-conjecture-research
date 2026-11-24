"""Exact controls for literal near-diagonal entry and quadratic descent."""
from std.testing import assert_true, assert_equal, assert_raises
from finite_exact.checked_int import checked_abs, checked_add, checked_mul, checked_sub
from mojo_smoke.claims import require_contract
from psc.bh_two_parameter_carrier import (
    build_carrier, parikh_difference, tables_for, verify_carrier,
)
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapAutomaton, SeedOverlapTables, cached_sign,
    first_depths, interior_overlap_cached, selected_overlap_child,
)
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_scale_checked, cubic_sub_checked


def _mass(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int], p: OverlapState) raises -> CubicElt:
    var left = p.shift if cached_sign(tables, signs, p.shift) > 0 else CubicElt()
    var b = cubic_add_checked(p.shift, tables.lengths.at(p.bottom))
    var a = tables.lengths.at(p.top)
    var right = a if cached_sign(tables, signs, cubic_sub_checked(b, a)) > 0 else b
    return cubic_sub_checked(right, left)


def _within(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
            value: CubicElt, limit: CubicElt) raises -> Bool:
    return cached_sign(tables, signs, cubic_sub_checked(limit, value)) >= 0 and (
        cached_sign(tables, signs, cubic_add_checked(limit, value)) >= 0
    )


def _energy(k: Int, r: Int, z: Int, y: Int) raises -> CubicElt:
    # beta times B*z*z + A*z*y + y*y in the same cubic embedding.
    var zy = checked_mul(z, y)
    return CubicElt(checked_mul(r, checked_mul(z, z)),
                    checked_sub(checked_mul(y, y), checked_mul(k, zy)), zy)


def _run_step(r: Int, k: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
              p: OverlapState) raises -> Tuple[Int, Int, OverlapState, Bool]:
    if r < 12 or k - r < 1 or k - r > 2:
        raise Error("quadratic-window proof applies to r>=12 and k-r=1,2")
    var limit = CubicElt(0, k - 1)
    if p.top != 1 or p.bottom != 1 or not _within(tables, signs, p.shift, limit):
        raise Error("source outside the central window")
    var delta = parikh_difference(r, p.shift)
    var x = delta.a0
    var y = delta.a1
    var z = delta.a2
    # beta^2*w = r*y + beta*(2*y + r*z).
    var w = CubicElt(checked_mul(r, y), checked_add(checked_mul(2, y), checked_mul(r, z)))
    var orientation = -1 if cached_sign(tables, signs, w) < 0 else 1
    var w_abs = cubic_scale_checked(w, orientation)
    var left = 0
    var right = checked_add(1, checked_add(checked_abs(z), checked_abs(y)))
    while right - left > 1:
        var mid = left + (right - left) // 2
        if cached_sign(tables, signs, cubic_sub_checked(w_abs, CubicElt(0, 0, mid))) >= 0:
            left = mid
        else:
            right = mid
    var rotated = -orientation * left
    var other = not _within(tables, signs, cubic_add_checked(w, CubicElt(0, 0, rotated)), limit)
    if other:
        rotated = checked_sub(rotated, orientation)
    var difference = checked_sub(rotated, checked_add(checked_add(x, checked_mul(k, y)), z))
    if checked_abs(difference) >= k:
        raise Error("rounding did not bind to actual run indices")
    var i = 1 + max(0, difference)
    var j = 1 + max(0, -difference)
    var child = selected_overlap_child(tables, p, i, j)
    var decoded = parikh_difference(r, child.shift)
    if child.top != 1 or child.bottom != 1 or not interior_overlap_cached(tables, signs, child):
        raise Error("actual digit pair did not produce a strict 1/1 child")
    if decoded != CubicElt(checked_add(y, checked_mul(r, z)), rotated, y):
        raise Error("wrong full-coordinate child")
    if not _within(tables, signs, child.shift, limit):
        raise Error("child left the central window")
    if y == 0 and z == 0:
        if not child.is_coincidence():
            raise Error("last step failed to clear the first coordinate")
    elif cached_sign(tables, signs, cubic_sub_checked(_energy(k, r, y, rotated),
                                                     _energy(k, r, z, y))) >= 0:
        raise Error("literal step failed strict quadratic descent")
    return (i, j, child, other)


def _replay_case(r: Int, k: Int) raises -> Int:
    var tables = tables_for(r, k)
    var carrier = build_carrier(r, k, 250000, 2500000)
    var receipt = verify_carrier(r, k, carrier)
    var signs = Dict[CubicElt, Int]()
    var half = List[Bool]()
    var unit_marks = List[Bool]()
    var adjacency = List[List[Int]]()
    var alternate = 0
    var central = 0
    for u in range(len(carrier.states)):
        var p = carrier.states[u]
        var w = _mass(tables, signs, p)
        half.append(cached_sign(tables, signs,
            cubic_sub_checked(cubic_scale_checked(w, 2), tables.lengths.at(0))) >= 0)
        unit_marks.append(p.top == 1 and p.bottom == 1 and cached_sign(tables, signs,
            cubic_sub_checked(cubic_scale_checked(w, 4), tables.lengths.at(1))) >= 0)
        var row = List[Int]()
        for e in carrier.rows[u]:
            row.append(e.target)
        adjacency.append(row^)
        if p.top == 1 and p.bottom == 1 and _within(tables, signs, p.shift, CubicElt(0, k-1)):
            var step = _run_step(r, k, tables, signs, p)
            var matched = False
            for e in carrier.rows[u]:
                if e.top_index == step[0] and e.bottom_index == step[1]:
                    assert_true(carrier.states[e.target] == step[2])
                    matched = True
            assert_true(matched)
            central += 1
            if step[3]:
                alternate += 1
    var graph = SeedOverlapAutomaton(carrier.states, adjacency, False)
    var to_half = first_depths(graph, half)
    var at_depth = unit_marks^
    for _ in range(3):
        var previous = List[Bool]()
        for row in graph.adj:
            var found = False
            for target in row:
                if at_depth[target]:
                    found = True
                    break
            previous.append(found)
        at_depth = previous^
    for u in range(graph.size()):
        assert_true(to_half[u] >= 0)
        if half[u]:
            assert_true(at_depth[u])
    print(r, k, graph.size(), receipt[0], central, alternate, sep=",")
    return alternate


def _endpoints() raises:
    var r = 12
    var k = 13
    var tables = tables_for(r, k)
    var signs = Dict[CubicElt, Int]()
    var at_bound = OverlapState(1, 1, CubicElt(0, -(k-1)))
    var step = _run_step(r, k, tables, signs, at_bound)
    assert_equal(step[0], 1)
    assert_equal(step[1], k)
    assert_true(step[2].is_coincidence())
    var on_contact = OverlapState(1, 1, CubicElt(0, 0, -1))
    assert_true(not interior_overlap_cached(tables, signs, on_contact))
    with assert_raises():
        _ = _run_step(r, k, tables, signs, on_contact)
    var diagonal_tables = tables_for(r, r)
    var diagonal_limit = OverlapState(1, 1, CubicElt(0, -r))
    var diagonal_signs = Dict[CubicElt, Int]()
    assert_true(interior_overlap_cached(diagonal_tables, diagonal_signs, diagonal_limit))
    assert_true(not _within(diagonal_tables, diagonal_signs, diagonal_limit.shift, CubicElt(0, r-1)))
    with assert_raises():
        _ = _run_step(r, r, diagonal_tables, diagonal_signs, diagonal_limit)


def main() raises:
    _endpoints()
    print("r,k,packets,occurrences,central,alternate")
    var alternate = 0
    for r in [12, 13, 16, 20]:
        for gap in [1, 2]:
            alternate += _replay_case(r, r + gap)
    assert_true(alternate > 0)
    print("verified entry and selected literal descent on eight exact swap closures")
    require_contract("Original occurrence ordinals and full displacement replay through run entry and quadratic descent on eight off-diagonal swap closures, including endpoint and strictness controls.")
