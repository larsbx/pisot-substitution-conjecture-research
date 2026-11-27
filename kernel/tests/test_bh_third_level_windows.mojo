"""Exact three-window selection with the two original digit triples."""
from std.testing import assert_true, assert_raises
from mojo_smoke.claims import require_contract
from psc.bh_two_parameter_carrier import parikh_difference, tables_for
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, cached_sign, interior_overlap_cached, selected_overlap_child,
)
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_mul_beta, cubic_scale_checked, cubic_sub_checked,
)


struct UnitMark(ImplicitlyCopyable, Copyable, Movable):
    var start: CubicElt
    var first: Int
    var second: Int
    var third: Int

    def __init__(out self, start: CubicElt, first: Int, second: Int, third: Int):
        self.start = start
        self.first = first
        self.second = second
        self.third = third


struct Track(Copyable, Movable):
    var end: CubicElt
    var twos: List[CubicElt]
    var units: List[UnitMark]

    def __init__(out self):
        self.end = CubicElt()
        self.twos = List[CubicElt]()
        self.units = List[UnitMark]()


def _track(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int], source: Int) raises -> Track:
    var track = Track()
    var unit = tables.lengths.at(1)
    var spacing = cubic_mul_beta(tables.field, cubic_mul_beta(tables.field, unit))
    for i in range(len(tables.sigma[source])):
        var a = tables.sigma[source][i]
        for j in range(len(tables.sigma[a])):
            var b = tables.sigma[a][j]
            if b == 2:
                if len(track.twos) > 0:
                    var gap = cubic_sub_checked(track.end, track.twos[len(track.twos)-1])
                    assert_true(cached_sign(tables, signs, cubic_sub_checked(gap, spacing)) >= 0)
                track.twos.append(track.end)
            for k in range(len(tables.sigma[b])):
                var c = tables.sigma[b][k]
                if c == 1:
                    track.units.append(UnitMark(track.end, i, j, k))
                track.end = cubic_add_checked(track.end, tables.lengths.at(c))
    var length = tables.lengths.at(source)
    for _ in range(3):
        length = cubic_mul_beta(tables.field, length)
    assert_true(track.end == length)
    return track^


def _clean(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
           track: Track, shift: CubicElt, left: CubicElt, right: CubicElt,
           block_bound: CubicElt) raises -> Bool:
    for p in track.twos:
        var start = cubic_add_checked(shift, p)
        if cached_sign(tables, signs, cubic_sub_checked(start, right)) >= 0:
            break
        var end = cubic_add_checked(start, block_bound)
        if cached_sign(tables, signs, cubic_sub_checked(end, left)) > 0:
            return False
    return True


def _unit_near(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
               track: Track, point_times_two: CubicElt, unit: CubicElt,
               short_gap: CubicElt) raises -> UnitMark:
    var lo = 0
    var hi = len(track.units)
    while lo < hi:
        var mid = lo + (hi-lo)//2
        var end = cubic_scale_checked(cubic_add_checked(track.units[mid].start, unit), 2)
        if cached_sign(tables, signs, cubic_sub_checked(end, point_times_two)) < 0:
            lo = mid + 1
        else:
            hi = mid
    if lo == len(track.units):
        raise Error("the chosen point has no current or following unit")
    var mark = track.units[lo]
    var limit = cubic_add_checked(point_times_two, cubic_scale_checked(short_gap, 2))
    if cached_sign(tables, signs, cubic_sub_checked(cubic_scale_checked(mark.start, 2), limit)) > 0:
        raise Error("gap to the original unit mark exceeds three short tiles")
    return mark


def _mass(tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int], p: OverlapState) raises -> CubicElt:
    var left = p.shift if cached_sign(tables, signs, p.shift) > 0 else CubicElt()
    var a = tables.lengths.at(p.top)
    var b = cubic_add_checked(p.shift, tables.lengths.at(p.bottom))
    var right = a if cached_sign(tables, signs, cubic_sub_checked(b, a)) >= 0 else b
    return cubic_sub_checked(right, left)


def _replay(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
            source: OverlapState, top: UnitMark, bottom: UnitMark, expected: CubicElt) raises:
    var p = selected_overlap_child(tables, source, top.first, bottom.first)
    assert_true(interior_overlap_cached(tables, signs, p))
    _ = parikh_difference(r, p.shift)
    p = selected_overlap_child(tables, p, top.second, bottom.second)
    assert_true(interior_overlap_cached(tables, signs, p))
    _ = parikh_difference(r, p.shift)
    p = selected_overlap_child(tables, p, top.third, bottom.third)
    assert_true(interior_overlap_cached(tables, signs, p))
    _ = parikh_difference(r, p.shift)
    assert_true(p == OverlapState(1, 1, expected))
    var m = cubic_scale_checked(_mass(tables, signs, p), 4)
    assert_true(cached_sign(tables, signs, cubic_sub_checked(m, tables.lengths.at(1))) >= 0)


def _select(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
            source: OverlapState, upper: Track, lower: Track,
            advance: CubicElt = CubicElt()) raises -> Int:
    var unit = tables.lengths.at(1)
    var short = tables.lengths.at(0)
    if cached_sign(tables, signs, cubic_sub_checked(
        cubic_scale_checked(_mass(tables, signs, source), 2), short)) < 0:
        raise Error("the source has less than half a short tile of overlap")
    var s = source.shift
    for _ in range(3):
        s = cubic_mul_beta(tables.field, s)
    assert_true(cached_sign(tables, signs, advance) >= 0)
    var first = s if cached_sign(tables, signs, s) > 0 else CubicElt()
    var start = cubic_add_checked(first, advance)
    var required_end = cubic_add_checked(start, cubic_scale_checked(unit, 18))
    assert_true(cached_sign(tables, signs, cubic_sub_checked(upper.end, required_end)) > 0)
    assert_true(cached_sign(tables, signs, cubic_sub_checked(
        cubic_add_checked(s, lower.end), required_end)) > 0)
    var bound = cubic_scale_checked(unit, 2)
    var gap = cubic_scale_checked(short, 3)
    for slot in range(3):
        var left = cubic_add_checked(start, cubic_scale_checked(unit, 7*slot))
        var right = cubic_add_checked(left, cubic_scale_checked(unit, 4))
        if not _clean(tables, signs, upper, CubicElt(), left, right, bound):
            continue
        if not _clean(tables, signs, lower, s, left, right, bound):
            continue
        var x2 = cubic_add_checked(cubic_scale_checked(left, 2), cubic_scale_checked(unit, 3))
        var top = _unit_near(tables, signs, upper, x2, unit, gap)
        var y2 = cubic_sub_checked(cubic_add_checked(cubic_scale_checked(top.start, 2), unit),
            cubic_scale_checked(s, 2))
        var bottom = _unit_near(tables, signs, lower, y2, unit, gap)
        var expected = cubic_sub_checked(cubic_add_checked(s, bottom.start), top.start)
        _replay(r, tables, signs, source, top, bottom, expected)
        return slot
    raise Error("all three windows were ruled out")


def main() raises:
    print("r,k,source_packets,first_window,second_window,third_window")
    for r in [12, 16, 20]:
        for k in range(r, r+3):
            var tables = tables_for(r, k)
            var signs = Dict[CubicElt, Int]()
            var tracks = List[Track]()
            for a in range(3):
                tracks.append(_track(tables, signs, a))
            if k == r:
                # At a common interior subwindow, the top and bottom
                # copies of the first 2 block rule out different slots.
                var source = OverlapState(1, 1, CubicElt(-3*r, 3))
                var shifted = source.shift
                for _ in range(3):
                    shifted = cubic_mul_beta(tables.field, shifted)
                var unit = tables.lengths.at(1)
                var anchor = cubic_sub_checked(tracks[1].twos[0], unit)
                var advance = cubic_sub_checked(anchor, shifted)
                assert_true(_select(r, tables, signs, source, tracks[1], tracks[1], advance) == 2)
            var wrong = UnitMark(CubicElt(), 1, 0, 0)
            with assert_raises():
                _replay(r, tables, signs, OverlapState(0, 0, CubicElt()), wrong, wrong, CubicElt())
            with assert_raises():
                _ = _select(r, tables, signs, OverlapState(0, 0, tables.lengths.at(0)),
                            tracks[0], tracks[0])
            var counts: List[Int] = [0, 0, 0]
            var cases = 0
            for a in range(3):
                for b in range(3):
                    for x in range(-r-1, r+2):
                        for y in range(-1, 2):
                            for z in range(-1, 2):
                                var p = OverlapState(a, b, CubicElt(-r*z, -x-z, -y))
                                if cached_sign(tables, signs, cubic_sub_checked(
                                    cubic_scale_checked(_mass(tables, signs, p), 2),
                                    tables.lengths.at(0))) < 0:
                                    continue
                                var slot = _select(r, tables, signs, p, tracks[a], tracks[b])
                                counts[slot] += 1
                                cases += 1
            assert_true(cases > 0)
            print(r, k, cases, counts[0], counts[1], counts[2], sep=",")
    print("exact third-level choices and the two original digit triples verified")
    require_contract("A selected common window replays three literal inflation steps on both tracks and preserves all displacement coordinates, with last-window, wrong-ordinal and contact controls.")
