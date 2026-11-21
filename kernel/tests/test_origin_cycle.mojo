"""The origin-tile recurrence of the literal family, exactly, on a box."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.origin_cycle import OriginSystem, cycle_census, interior_cycles, pack_tile, unpack_tile


def phases() raises -> List[Int]:
    return [pack_tile(1, -1, 1, 0), pack_tile(1, 0, 0, 1), pack_tile(1, 1, 0, 0)]


def test_signs_and_children() raises:
    var s = OriginSystem(2)
    assert_equal(unpack_tile(pack_tile(2, -7, 0, 5)), List[Int]([2, -7, 0, 5]))
    assert_equal(s.length_sign(0, 0, 0), 0)
    # beta lies in (2, 3) at k = 2: 2 beta < beta^2 < 3 beta, and beta + 2 < beta^2.
    assert_equal(s.length_sign(-2, 1, 0), 1)
    assert_equal(s.length_sign(-3, 1, 0), -1)
    assert_equal(s.length_sign(0, 1, -1), 1)
    # The three phases, in orbit order: starts -l0, l0 - l1, -l2.
    assert_equal(s.child(pack_tile(1, 1, 0, 0)), pack_tile(1, -1, 1, 0))
    assert_equal(s.child(pack_tile(1, -1, 1, 0)), pack_tile(1, 0, 0, 1))
    assert_equal(s.child(pack_tile(1, 0, 0, 1)), pack_tile(1, 1, 0, 0))
    assert_true(s.is_interior(1, 1, 0, 0))
    # A vertex is not interior, and neither is a tile ending at the origin.
    assert_false(s.is_interior(1, 0, 0, 0))
    assert_false(s.is_interior(1, 0, 1, 0))
    assert_false(s.is_interior(0, 1, 0, 0))
    # An interior tile can inflate to a vertex: l.(-1,0,1) = 2 and 2 beta
    # is the start of the third child of sigma(2). The vertex then persists.
    assert_true(s.is_interior(2, -1, 0, 1))
    assert_equal(s.child(pack_tile(2, -1, 0, 1)), pack_tile(1, 0, 0, 0))
    assert_equal(s.child(pack_tile(1, 0, 0, 0)), pack_tile(0, 0, 0, 0))
    assert_equal(s.child(pack_tile(0, 0, 0, 0)), pack_tile(1, 0, 0, 0))


def test_unique_cycle() raises:
    for k in range(2, 7):
        var s = OriginSystem(k)
        var census = cycle_census(s, 5, 4096)
        assert_true(census.tiles > 0)
        # The other cycle reached is the vertex cycle (0;0,0,0) -> (1;0,0,0).
        assert_equal(len(census.cycles), 2)
        var interior = interior_cycles(census)
        assert_equal(len(interior), 1)
        assert_equal(interior[0], phases())


def test_parameter_one_control() raises:
    # At k = 1 the second child of the phase at -l2 has type 2: the
    # three-phase cycle does not exist and an eight-cycle takes its place.
    var s = OriginSystem(1)
    assert_equal(s.child(pack_tile(1, 0, 0, 1)), pack_tile(2, 1, 0, 0))
    var census = cycle_census(s, 5, 4096)
    var interior = interior_cycles(census)
    assert_equal(len(interior), 1)
    assert_equal(len(interior[0]), 8)
    assert_equal(interior[0][0], pack_tile(0, 1, -1, 1))


def test_refusals() raises:
    var refused = False
    try:
        var s = OriginSystem(0)
        _ = s.k
    except e:
        refused = True
    assert_true(refused)
    refused = False
    var s = OriginSystem(2)
    try:
        _ = cycle_census(s, 5, 2)
    except e:
        refused = True
    assert_true(refused)
    refused = False
    try:
        # A tile that does not cover the origin has no origin child.
        _ = s.child(pack_tile(0, 3, 0, 0))
    except e:
        refused = True
    assert_true(refused)


def main() raises:
    test_signs_and_children()
    test_unique_cycle()
    test_parameter_one_control()
    test_refusals()
    require_contract("The origin-tile recurrence of 0 -> 1, 1 -> 0 1^k 2, 2 -> 001 is evaluated by exact sign queries at beta. For k = 2..6 every interior lattice tile with coordinates of absolute value at most 5 reaches the three-phase cycle (1;1,0,0) -> (1;-1,1,0) -> (1;0,0,1) or the vertex cycle (0;0,0,0) -> (1;0,0,0) and no other cycle; at k = 1 the three-phase cycle does not exist and the only interior cycle the same box reaches is one eight-cycle. A step cap, a parameter below one and a tile not covering the origin raise. Box-bounded finite evidence; periodic tiles outside the box are not excluded.")
