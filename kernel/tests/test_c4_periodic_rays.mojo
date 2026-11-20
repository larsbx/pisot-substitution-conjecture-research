"""Replay the complete cyclic-root decisions and their two-track addresses."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import newborn_sync_positions
from psc.c4_addressed_newborn import addressed_newborn
from psc.c4_periodic_rays import (
    common_endpoint_depth, decide_periodic_rays, first_forbidden_hub_start, has_common_endpoint,
)
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapAutomaton, build_seed_overlap_tables_screened, interior_overlap,
)
from psc.perron_field3 import cubic_sub_checked
from psc.words import Pair


def digits(xs: List[Int]) -> String:
    if len(xs) == 0:
        return String("-")
    var out = String("")
    for i in range(len(xs)):
        out += "," + String(xs[i])
    return out^


def check_source(
    name: String, sigma: List[List[Int]], top: List[Int], bottom: List[Int],
    depths: List[Int],
) raises:
    var result = decide_periodic_rays(sigma)
    assert_equal(len(result), len(depths))
    for i in range(len(result)):
        ref ray = result[i]
        assert_equal(ray.top, top[i])
        assert_equal(ray.bottom, bottom[i])
        assert_equal(ray.coincidence_depth, depths[i])
        assert_equal(ray.boundary_depth, -1)
        assert_equal(len(ray.top_digits), depths[i])
        assert_equal(len(ray.bottom_digits), depths[i])
        assert_false(ray.has_strict_system())
        print("RAY", name, ray.top, ray.bottom, ray.state_count, ray.occurrence_count,
              ray.coincidence_depth, ray.boundary_depth, digits(ray.top_digits),
              digits(ray.bottom_digits))


def check_boundary_distance() raises:
    # Synthetic rows test only the distance consumer. The two vertices are
    # geometrically valid and the only target is right-aligned.
    var sigma: List[List[Int]] = [[1], [0, 2, 1], [0, 0, 1]]
    var tables = build_seed_overlap_tables_screened(sigma)
    var right_offset = cubic_sub_checked(tables.lengths.at(0), tables.lengths.at(1))
    var right_only = OverlapState(0, 1, right_offset)
    var interior = OverlapState(2, 1, tables.lengths.at(0))
    assert_true(interior_overlap(tables, interior))
    assert_false(has_common_endpoint(tables, interior))
    var states: List[OverlapState] = [interior, right_only]
    var with_endpoint: List[List[Int]] = [[1], []]
    var without_endpoint: List[List[Int]] = [[0], []]
    assert_equal(common_endpoint_depth(tables, SeedOverlapAutomaton(states, with_endpoint, False)), 1)
    assert_equal(common_endpoint_depth(tables, SeedOverlapAutomaton(states, without_endpoint, False)), -1)


def check_phase(
    name: String, sigma: List[List[Int]], hub: Int, phase: Int, depth: Int,
) raises:
    var witness = first_forbidden_hub_start(sigma, hub, 0, 1, phase)
    assert_equal(witness.depth, depth)
    assert_equal(len(witness.top_digits), depth)
    assert_equal(len(witness.bottom_digits), depth)
    print("PHASE", name, depth, witness.top, witness.bottom,
          digits(witness.top_digits), digits(witness.bottom_digits))


def main() raises:
    check_boundary_distance()
    check_source("left-proper-power", [[0, 1], [0, 2], [0]], [], [], [])
    var phase_zero: List[List[Int]] = [[0, 1], [1, 2], [0, 2, 1]]
    check_source("phase-zero", phase_zero, [0], [1], [4])
    check_phase("fixed-hub", phase_zero, 1, 0, 3)
    var swapping: List[List[Int]] = [[1], [0, 2], [0, 0, 2]]
    check_phase("swapping-hub", swapping, 0, 1, 5)
    assert_equal(first_forbidden_hub_start(swapping, 0, 0, 1, 0).depth, 1)
    var ray = decide_periodic_rays(phase_zero)[0].copy()
    var birth = addressed_newborn(
        phase_zero, Pair([0, 1], [1, 0]), 0, 0, ray.top_digits, ray.bottom_digits,
    )
    assert_equal(birth.ordinals, [0, 0, 1, 0])
    assert_equal(birth.cut, 1)
    assert_false(birth.sync_right)
    assert_true(birth.cut in newborn_sync_positions(phase_zero, birth.parent))

    var nonunit: List[List[Int]] = [[1], [0, 2, 1], [0, 0, 1]]
    check_source("nonunit-period-two", nonunit, [0], [1], [5])
    check_source("three-cyclic-letters", [[1], [2, 0, 1], [0, 0, 1]],
                 [0, 0, 1], [1, 2, 2], [5, 6, 4])
    check_source("parameter-three", [[1], [0, 1, 1, 1, 2], [0, 0, 1]],
                 [0], [1], [2])

    var tables = build_seed_overlap_tables_screened(nonunit)
    var offset = cubic_sub_checked(tables.lengths.at(0), tables.lengths.at(1))
    var right_only = OverlapState(0, 1, offset)
    assert_false(offset.is_zero())
    assert_true(interior_overlap(tables, right_only))
    assert_true(has_common_endpoint(tables, right_only))
    assert_false(interior_overlap(tables, OverlapState(0, 1, tables.lengths.at(0))))

    var refused = False
    try:
        _ = decide_periodic_rays(phase_zero, 1)
    except:
        refused = True
    assert_true(refused)

    refused = False
    try:
        var reducible: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
        _ = decide_periodic_rays(reducible)
    except:
        refused = True
    assert_true(refused)
    require_contract("complete periodic-ray overlap decisions with literal coincidence addresses and both closed endpoints")
    require_contract("phase-aware periodic-ray starts preserve hub orientation at every generation or return a literal violating address")
