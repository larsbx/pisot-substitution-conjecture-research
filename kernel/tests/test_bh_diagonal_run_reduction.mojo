"""Literal choices for the sufficient central region at determinant r=k."""
from std.testing import assert_true, assert_equal, assert_raises
from finite_exact.checked_int import checked_abs, checked_add, checked_mul, checked_sub
from mojo_smoke.claims import require_contract
from psc.bh_two_parameter_carrier import parikh_difference, tables_for
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, cached_sign, interior_overlap_cached, selected_overlap_child,
)
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_scale_checked, cubic_sub_checked


def _within(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
            shift: CubicElt, radius: CubicElt) raises -> Bool:
    return cached_sign(tables, signs, cubic_sub_checked(radius, shift)) >= 0 and (
        cached_sign(tables, signs, cubic_add_checked(radius, shift)) >= 0
    )


def _packet(r: Int, x: Int, y: Int, z: Int) raises -> OverlapState:
    return OverlapState(1, 1, cubic_scale_checked(
        CubicElt(checked_mul(r, z), checked_add(x, z), y), -1))


def _run(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
         state: OverlapState, t: Int, remain_in_window: Bool = True) raises -> OverlapState:
    var d = parikh_difference(r, state.shift)
    var h = checked_sub(t, checked_add(checked_add(d.a0, checked_mul(r, d.a1)), d.a2))
    if checked_abs(h) >= r:
        raise Error("rounding has no two literal run positions")
    var next = selected_overlap_child(tables, state, 1 + max(0, h), 1 + max(0, -h))
    var expected = _packet(r, checked_add(d.a1, checked_mul(r, d.a2)), t, d.a1)
    if next != expected or not interior_overlap_cached(tables, signs, next):
        raise Error("requested child is not the claimed full strict run packet")
    if remain_in_window and not _within(tables, signs, next.shift, CubicElt(0, r - 1)):
        raise Error("requested run child leaves the window")
    return next


def _turn(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
          state: OverlapState) raises -> OverlapState:
    return _run(r, tables, signs, state, checked_sub(0, parikh_difference(r, state.shift).a2))


def _reduce(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
            state: OverlapState) raises -> OverlapState:
    var d = parikh_difference(r, state.shift)
    if not (d.a1 > 0 and d.a2 < 0 or d.a1 < 0 and d.a2 > 0):
        raise Error("absolute-coordinate reduction requires opposite nonzero signs")
    return _run(r, tables, signs, state, checked_sub(1 if d.a2 > 0 else -1, d.a2))


def _unit_exit(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
               packet: OverlapState) raises -> OverlapState:
    if packet != _packet(r, r, 0, 0):
        raise Error("unit-axis exit requires the exact saturated packet")
    var mixed = selected_overlap_child(tables, packet, 1, r + 1)
    if mixed != OverlapState(1, 2, CubicElt()) or not interior_overlap_cached(tables, signs, mixed):
        raise Error("the ordered end pair must give strict 1/2 zero")
    var zero = selected_overlap_child(tables, mixed, 0, 0)
    if zero != OverlapState(0, 0, CubicElt()) or not interior_overlap_cached(tables, signs, zero):
        raise Error("the two first letters must give labelled zero")
    return zero


def _trace(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
           source: OverlapState) raises -> Int:
    var limit = (r - 2) // 3
    var d = parikh_difference(r, source.shift)
    if r < 12 or source.top != 1 or source.bottom != 1 or (
        not _within(tables, signs, source.shift, CubicElt(0, r - 1))
    ) or max(checked_abs(d.a1), checked_abs(d.a2)) > limit:
        raise Error("outside the proved diagonal sufficient region")
    var initial = checked_add(checked_abs(d.a1), checked_abs(d.a2))
    var steps = 0
    var p = source
    while True:
        d = parikh_difference(r, p.shift)
        var m = checked_add(checked_abs(d.a1), checked_abs(d.a2))
        if m == 0:
            assert_true(_run(r, tables, signs, p, 0).is_coincidence())
            assert_true(steps + 1 <= 7 * initial + 8)
            return steps + 1
        if d.a1 != 0 and d.a2 != 0:
            if (d.a1 > 0) == (d.a2 > 0):
                p = _turn(r, tables, signs, p)
                steps += 1
            p = _reduce(r, tables, signs, p)
            steps += 1
        else:
            for _ in range(3):
                if d.a2 == 0 and d.a1 < 0:
                    break
                p = _turn(r, tables, signs, p)
                steps += 1
                d = parikh_difference(r, p.shift)
            assert_true(d.a2 == 0 and d.a1 == -m)
            p = _run(r, tables, signs, p, 1)
            p = _reduce(r, tables, signs, p)
            steps += 2
            if m == 1:
                p = _run(r, tables, signs, p, 0, False)
                assert_true(_unit_exit(r, tables, signs, p).is_coincidence())
                assert_true(steps + 3 <= 7 * initial + 8)
                return steps + 3
            p = _turn(r, tables, signs, p)
            p = _reduce(r, tables, signs, p)
            steps += 2
        d = parikh_difference(r, p.shift)
        assert_true(max(checked_abs(d.a1), checked_abs(d.a2)) <= limit)
        assert_equal(checked_add(checked_abs(d.a1), checked_abs(d.a2)), m - 1)


def _extreme_x(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
               y: Int, z: Int, side: Int) raises -> Int:
    var x = z - r*y
    var lo = 0
    var hi = 2*r + 1
    # Search for the first or last admissible first coordinate, using exact signs.
    assert_true(_within(tables, signs, _packet(r, x, y, z).shift, CubicElt(0, r - 1)))
    while hi-lo > 1:
        var mid = lo + (hi-lo)//2
        if _within(tables, signs, _packet(r, x+side*mid, y, z).shift, CubicElt(0, r-1)):
            lo = mid
        else:
            hi = mid
    return x + side*lo


def _check_outer(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
                 source: OverlapState) raises -> Int:
    var p = source
    var old_rank = CubicElt()
    var other = 0
    var steps = 0
    while True:
        var d = parikh_difference(r, p.shift)
        var y = d.a1
        var z = d.a2
        # beta*Q, using beta*A=beta^2-r*beta.
        var rank = CubicElt(r*z*z, y*y-r*z*y, z*y)
        if steps > 0:
            assert_true(cached_sign(tables, signs, cubic_sub_checked(rank, old_rank)) < 0)
        if cached_sign(tables, signs, cubic_sub_checked(rank, CubicElt(0, r*r))) <= 0:
            return other
        # beta^2*w = r*y + beta*(2*y+r*z).
        var w = CubicElt(r*y, 2*y+r*z)
        var orientation = -1 if cached_sign(tables, signs, w) < 0 else 1
        var value = cubic_scale_checked(w, orientation)
        var lo = 0
        var hi = checked_abs(y) + checked_abs(z) + 1
        while hi-lo > 1:
            var mid = lo + (hi-lo)//2
            if cached_sign(tables, signs, cubic_sub_checked(value, CubicElt(0, 0, mid))) >= 0:
                lo = mid
            else:
                hi = mid
        var t = -orientation*lo
        if not _within(tables, signs, cubic_add_checked(w, CubicElt(0, 0, t)), CubicElt(0, r-1)):
            t -= orientation
            other += 1
        p = _run(r, tables, signs, p, t)
        old_rank = rank
        steps += 1
        if steps > 10000:
            raise Error("outer energy replay exceeded its control budget")


def main() raises:
    print("r,source_packets,max_edges,outer_alternate")
    var alternates = 0
    for r in [12, 13, 16, 20, 32]:
        var tables = tables_for(r, r)
        var signs = Dict[CubicElt, Int]()
        var limit = (r-2)//3
        var count = 0
        var longest = 0
        for z in range(-limit, limit + 1):
            for y in range(-limit, limit + 1):
                var left = _extreme_x(r, tables, signs, y, z, -1)
                var right = _extreme_x(r, tables, signs, y, z, 1)
                for x in [left, z-r*y, right]:
                    longest = max(longest, _trace(r, tables, signs, _packet(r, x, y, z)))
                    count += 1
        var initial = _packet(r, 1, 0, 1)
        var p = initial
        for _ in range(4):
            assert_true(not p.is_coincidence())
            p = _turn(r, tables, signs, p)
            assert_true(_within(tables, signs, cubic_scale_checked(p.shift, 2), tables.lengths.at(1)))
        assert_true(p == initial)
        # The small-box proof has a different hypothesis from outer descent.
        # Extreme-x calibration is only called from the small box. Assemble
        # another window representative at y=0,z=r+1, with cancelling x.
        var high = _packet(r, -2*r-1, 0, r+1)
        assert_true(_within(tables, signs, high.shift, CubicElt(0, r-1)))
        with assert_raises():
            _ = _trace(r, tables, signs, high)
        var other = _check_outer(r, tables, signs, high)
        for y in [r+1, r+2, r+3]:
            var outer = _packet(r, -r*y, y, 0)
            assert_true(_within(tables, signs, outer.shift, CubicElt(0, r-1)))
            other += _check_outer(r, tables, signs, outer)
        alternates += other
        print(r, count, longest, other, sep=",")
    assert_true(alternates > 0)
    print("small-box paths, exact four-cycles, and strict outer descents verified")
    require_contract("Literal run choices reach labelled coincidence from the tested diagonal small-box packets and escape nearest-rounding four-cycles. The outer controls decrease the quadratic energy strictly.")
