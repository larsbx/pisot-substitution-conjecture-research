"""Adversarial bounded native cover checks, separate from theorem admission."""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.rat_q import Q
from mojo_smoke.claims import require_contract
from psc.c4_finite_cylinder_overlap import (
    CylinderCertificate, GridBox, build_certificate, certify_radius,
    find_strong_coincidence, grid_ceil, grid_floor, intersection_area,
    make_chart, pair_upper, validate_certificate,
    certify_equation_11, strict_arithmetic_gap,
)
from psc.c4_cylinder_density import density_chart_name
from psc.words import Pair


def must_refuse(certificate: CylinderCertificate) raises:
    var refused = False
    try:
        validate_certificate(certificate)
    except:
        refused = True
    assert_true(refused)


def test_complete_controls() raises:
    var total = 0
    for fixture in range(2):
        var chart = make_chart()
        certify_radius(fixture, chart)
        assert_true(Q.zero().lt(chart.kappa.lo))
        for depth in range(2, 7, 2):
            var certificate = build_certificate(fixture, depth)
            validate_certificate(certificate)
            total += len(certificate.occurrences)
            if fixture == 0:
                assert_true(pair_upper(certificate, 0, 2).eq(Q.zero()))
                assert_true(pair_upper(certificate, 1, 2).eq(Q.zero()))
            assert_true(Q.zero().lt(pair_upper(certificate, 0, 1)))
        for first in range(3):
            for second in range(first + 1, 3):
                var witness = find_strong_coincidence(fixture, first, second)
                assert_true(witness.depth >= 1 and witness.depth <= 6)
    assert_equal(total, 1002)


def test_occurrence_adversaries() raises:
    var canonical = build_certificate(0, 4)
    var bad = canonical.copy()
    _ = bad.occurrences.pop()
    must_refuse(bad)
    bad = canonical.copy()
    bad.occurrences[1] = bad.occurrences[0].copy()
    must_refuse(bad)
    bad = canonical.copy()
    bad.occurrences[1].position += 1
    must_refuse(bad)
    bad = canonical.copy()
    bad.occurrences[1].prefix[0] += 1
    must_refuse(bad)
    bad = canonical.copy()
    bad.occurrences[1].key[0] = (bad.occurrences[1].key[0] + 1) % bad.index
    must_refuse(bad)
    bad = canonical.copy()
    # Coordinate reduction of the adjugate key is not quotient refinement.
    var changed = False
    for i in range(len(bad.occurrences)):
        for j in range(3):
            var wrong = bad.occurrences[i].key[j] % 4
            if wrong != bad.occurrences[i].parent[j]:
                bad.occurrences[i].parent[j] = wrong
                changed = True
                break
        if changed:
            break
    assert_true(changed)
    must_refuse(bad)


def test_enclosure_adversaries() raises:
    var canonical = build_certificate(0, 2)
    var bad = canonical.copy()
    bad.occurrences[0].box.xlo += 1
    must_refuse(bad)
    bad = canonical.copy()
    bad.occurrences[0].box.ylo = bad.occurrences[0].box.yhi + 1
    must_refuse(bad)
    bad = canonical.copy()
    bad.slices[0].box.xhi -= 1
    must_refuse(bad)
    bad = canonical.copy()
    bad.index *= 2
    must_refuse(bad)
    bad = canonical.copy()
    bad.period = 1
    must_refuse(bad)
    var chart = make_chart()
    chart.radius = 39
    var refused = False
    try:
        certify_radius(0, chart)
    except:
        refused = True
    assert_true(refused)
    chart = make_chart()
    chart.kappa.lo = Q.one()
    refused = False
    try:
        certify_radius(0, chart)
    except:
        refused = True
    assert_true(refused)


def test_caps_and_rounding() raises:
    for fixture in range(-1, 3):
        if fixture == 0 or fixture == 1:
            continue
        var refused = False
        try:
            _ = build_certificate(fixture, 2)
        except:
            refused = True
        assert_true(refused)
    for depth in range(0, 9):
        if depth == 2 or depth == 4 or depth == 6:
            continue
        var refused = False
        try:
            _ = build_certificate(0, depth)
        except:
            refused = True
        assert_true(refused)
    var refused = False
    try:
        _ = build_certificate(0, 2, 2, 1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = build_certificate(0, 2, 2, 2187, 1)
    except:
        refused = True
    assert_true(refused)
    assert_equal(grid_floor(Q(-1, 3)), -6)
    assert_equal(grid_ceil(Q(-1, 3)), -5)
    assert_equal(grid_floor(Q(1, 2)), 8)
    assert_equal(grid_ceil(Q(1, 2)), 8)
    assert_true(intersection_area(GridBox(0, 16, 0, 16), GridBox(16, 32, 0, 16)).eq(Q.zero()))


def test_equation_eleven_cannot_invent_its_density_premise() raises:
    assert_true(strict_arithmetic_gap(Q.zero(), Q.one(), Q(1, 100)).eq(Q(1, 100)))
    var refused = False
    try:
        _ = strict_arithmetic_gap(Q.one(), Q(2, 1), Q(1, 2))
    except:
        refused = True
    assert_true(refused)  # Equality is not a strict contradiction.
    refused = False
    try:
        _ = strict_arithmetic_gap(Q.zero(), Q.one(), Q.zero())
    except:
        refused = True
    assert_true(refused)
    var certificate = build_certificate(0, 2)
    assert_true(pair_upper(certificate, 0, 2).eq(Q.zero()))
    var empty = List[Pair]()
    refused = False
    try:
        _ = certify_equation_11(certificate, empty, 0, 2, 1, Q(1, 100), density_chart_name())
    except:
        refused = True
    assert_true(refused)
    var false_system: List[Pair] = [Pair([0, 2], [2, 0])]
    refused = False
    try:
        _ = certify_equation_11(certificate, false_system, 0, 2, 1, Q(1, 100), density_chart_name())
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = certify_equation_11(certificate, false_system, 0, 2, 1, Q(1, 100), String("unit-covolume"))
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_complete_controls()
    test_occurrence_adversaries()
    test_enclosure_adversaries()
    test_caps_and_rounding()
    test_equation_eleven_cannot_invent_its_density_premise()
    print("[PASS] bounded complete cylinders, certified boxes, exact overlap uppers and adversarial refusals")
    require_contract("Two named period-two controls, depths 2/4/6: complete occurrence-indexed residue slices, certified fixed-radius rational boxes and finite overlap upper bounds; equation eleven requires authenticated literal strict-density premises and strict separation; no measure proof or general C4 claim")
