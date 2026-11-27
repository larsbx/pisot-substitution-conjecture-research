"""Bounded exact diagonal residual certificates and literal path controls."""
from std.testing import assert_equal, assert_raises, assert_true
from finite_exact.checked_int import checked_abs
from finite_exact.closed_interval import IQ
from mojo_smoke.claims import require_contract
from psc.bh_diagonal_residual import (
    _digits, build_residual_certificate, packet, pair_index,
    sample_first_coordinates, small_box, trace_residual_to_box, root_bracket,
    bracket_sign, bracket_within, run_edge, energy,
    verify_residual_certificate, verify_run_edge, within,
)
from psc.bh_two_parameter_carrier import parikh_difference, tables_for
from psc.exact import interval_horner_int, strict_sign
from psc.occurrence_path import OccurrenceEdge
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_sub_checked
from psc.perron_root_sign import perron_root_bracket
from test_bh_diagonal_run_reduction import _trace as small_box_trace


def test_interval_enumeration() raises:
    var r = 12
    var tables = tables_for(r, r)
    var beta_box = root_bracket(tables)
    var signs = Dict[CubicElt, Int]()
    var reference_signs = Dict[CubicElt, Int]()
    for z in range(-r, r + 1):
        for y in range(-r, r + 1):
            var digits = _digits(r, tables, signs, beta_box, z, y)
            var expected = List[Int]()
            # Independent full integer scan, without monotone search.
            var w = CubicElt(r*y, 2*y+r*z)
            for t in range(-r, r + 1):
                if within(tables, reference_signs, cubic_add_checked(w, CubicElt(0, 0, t)), CubicElt(0, r-1)):
                    expected.append(t)
            assert_equal(len(digits), len(expected))
            for i in range(len(digits)):
                assert_equal(digits[i], expected[i])


def test_refusals() raises:
    with assert_raises():
        _ = build_residual_certificate(11, 1000, 10000)
    with assert_raises():
        _ = build_residual_certificate(12, 624, 10000)
    with assert_raises():
        _ = build_residual_certificate(12, 1000, 0)
    var certificate = build_residual_certificate(12, 1000, 10000)
    var src = pair_index(12, 0, 11)
    var rank = certificate.ranks[src]
    assert_true(rank > 0)
    certificate.ranks[src] = 0
    with assert_raises():
        _ = verify_residual_certificate(certificate)
    certificate.ranks[src] = -1
    with assert_raises():
        _ = verify_residual_certificate(certificate)
    certificate.ranks[src] = rank + 1
    with assert_raises():
        _ = verify_residual_certificate(certificate)
    certificate.ranks[src] = rank
    var digit = certificate.next_t[src]
    certificate.next_t[src] = 13
    with assert_raises():
        _ = verify_residual_certificate(certificate)
    certificate.next_t[src] = digit
    certificate.edge_count += 1
    with assert_raises():
        _ = verify_residual_certificate(certificate)
    certificate.edge_count -= 1
    assert_equal(verify_residual_certificate(certificate)[1], 0)
    var tables = tables_for(12, 12)
    var beta_box = root_bracket(tables)
    var signs = Dict[CubicElt, Int]()
    # An enclosure touching zero must fall back, rather than guess its sign.
    var broad = perron_root_bracket(-12, -2, -12, 0)
    assert_equal(strict_sign(interval_horner_int([-12, 1], broad)), 0)
    assert_equal(bracket_sign(tables, signs, broad, CubicElt(-12, 1)), 1)
    var source = packet(12, -132, 11, 0)
    with assert_raises():
        _ = trace_residual_to_box(certificate, tables, signs, beta_box, source, 0)
    with assert_raises():
        _ = trace_residual_to_box(certificate, tables, signs, beta_box, OverlapState(1, 1, CubicElt(1)), 1000)
    with assert_raises():
        _ = trace_residual_to_box(certificate, tables, signs, beta_box, packet(12, 1000, 11, 0), 1000)
    # The earlier small-box center z-r*y is not a general residual center.
    assert_true(not within(tables, signs, packet(12, 7-12*8, 8, 7).shift, CubicElt(0, 11)))
    var samples = sample_first_coordinates(12, tables, signs, beta_box, 7, 8)
    assert_true(within(tables, signs, packet(12, samples[1], 8, 7).shift, CubicElt(0, 11)))
    var path = trace_residual_to_box(certificate, tables, signs, beta_box, source, 1000)
    assert_equal(len(path), rank)
    var edge = path[0]
    var t = parikh_difference(12, edge.target.shift).a1
    var target_counts = parikh_difference(12, edge.target.shift)
    with assert_raises():
        verify_run_edge(12, tables, signs, beta_box,
            OccurrenceEdge(edge.source, 0, edge.bottom_index, edge.target), t)
    with assert_raises():
        verify_run_edge(12, tables, signs, beta_box,
            OccurrenceEdge(edge.source, edge.top_index, 13, edge.target), t)
    with assert_raises():
        verify_run_edge(12, tables, signs, beta_box,
            OccurrenceEdge(edge.source, edge.top_index, edge.bottom_index,
                OverlapState(0, 0, CubicElt())), t)
    with assert_raises():
        verify_run_edge(12, tables, signs, beta_box,
            OccurrenceEdge(edge.source, edge.top_index, edge.bottom_index,
                packet(12, target_counts.a0+1, target_counts.a1, target_counts.a2)), t)
    with assert_raises():
        verify_run_edge(12, tables, signs, beta_box,
            OccurrenceEdge(edge.source, 1 if edge.top_index != 1 else 2,
                edge.bottom_index, edge.target), t)
    with assert_raises():
        verify_run_edge(12, tables, signs, beta_box, edge, t+1)


def test_residual_local_minima(r: Int, tables: SeedOverlapTables, mut signs: Dict[CubicElt, Int],
                               beta_box: IQ) raises -> Tuple[Int, Int, Int]:
    var minima = 0
    var nonaxis = 0
    var literal_edges = 0
    for z in range(-r, r+1):
        for y in range(-r, r+1):
            if z*z+y*y >= r*r or (z == 0 and y == 0):
                continue
            var initial = energy(r, z, y)
            var w = CubicElt(r*y, 2*y+r*z)
            var radius = CubicElt(0, r-1)
            # Both endpoints lie strictly outside admissibility; monotonicity
            # makes this larger digit interval a complete one-step scan.
            assert_true(bracket_sign(tables, signs, beta_box,
                cubic_add_checked(cubic_add_checked(w, CubicElt(0, 0, -2*r)), radius)) < 0)
            assert_true(bracket_sign(tables, signs, beta_box,
                cubic_sub_checked(cubic_add_checked(w, CubicElt(0, 0, 2*r)), radius)) > 0)
            var descends = False
            var digits = _digits(r, tables, signs, beta_box, z, y, 2*r)
            assert_true(len(digits) > 0)
            for t in digits:
                if bracket_sign(tables, signs, beta_box,
                    cubic_sub_checked(energy(r, y, t), initial)) < 0:
                    descends = True
            if descends:
                continue
            minima += 1
            var macro = List[Int]()
            if y == 0:
                if checked_abs(z) == 1:
                    continue  # Existing small-box replay checks the labelled unit exit.
                var orientation = 1 if z > 0 else -1
                macro.append(-z)
                macro.append(orientation)
                macro.append(z-orientation)
            else:
                nonaxis += 1
                assert_equal(r % 3, 0)
                var n = r//3
                var orientation = 1 if z > 0 else -1
                if orientation*z == n-1 and orientation*y == n:
                    macro.append(-orientation*n)
                    macro.append(orientation*(1-n))
                else:
                    assert_equal(orientation*z, n+2)
                    assert_equal(orientation*y, -n)
                    macro.append(orientation*(-n-1))
                    macro.append(orientation*(n+1))
            assert_true(len(macro) <= 3)
            var samples = sample_first_coordinates(r, tables, signs, beta_box, z, y)
            for x in [samples[0], samples[1], samples[2]]:
                var current = packet(r, x, y, z)
                for t in macro:
                    current = run_edge(r, tables, signs, beta_box, current, t).target
                    literal_edges += 1
                var d = parikh_difference(r, current.shift)
                assert_true(bracket_sign(tables, signs, beta_box,
                    cubic_sub_checked(energy(r, d.a2, d.a1), initial)) < 0)
    assert_equal(nonaxis, 4 if r%3 == 0 else 0)
    return (minima, nonaxis, literal_edges)


def main() raises:
    test_interval_enumeration()
    test_refusals()
    print("r,square_states,edges,disk_pairs,uncovered_disk,uncovered_square,max_rank,source_packets,max_total_edges")
    var all_pairs = 0
    var all_packets = 0
    for r in [12, 13, 15, 16, 18, 20, 32]:
        var certificate = build_residual_certificate(r, 10000, 30000)
        var receipt = verify_residual_certificate(certificate)
        # This finite result covers exactly these parameters and this disk.
        assert_equal(receipt[1], 0)
        var tables = tables_for(r, r)
        var beta_box = root_bracket(tables)
        var signs = Dict[CubicElt, Int]()
        var local = test_residual_local_minima(r, tables, signs, beta_box)
        var packets = 0
        var maximum = 0
        for z in range(-r, r + 1):
            for y in range(-r, r + 1):
                if z*z+y*y >= r*r:
                    continue
                var coordinates = sample_first_coordinates(r, tables, signs, beta_box, z, y)
                for x in [coordinates[0], coordinates[1], coordinates[2]]:
                    var source = packet(r, x, y, z)
                    var path = trace_residual_to_box(certificate, tables, signs, beta_box, source, 10000)
                    assert_equal(len(path), certificate.ranks[pair_index(r, z, y)])
                    var endpoint = source if len(path) == 0 else path[len(path)-1].target
                    var d = parikh_difference(r, endpoint.shift)
                    assert_true(small_box(r, d.a2, d.a1))
                    # Reuse the prior small-box executable instead of duplicating it.
                    var finish = small_box_trace(r, tables, signs, endpoint)
                    maximum = max(maximum, len(path)+finish)
                    packets += 1
        assert_equal(packets, 3*receipt[0])
        all_pairs += receipt[0]
        all_packets += packets
        print(r, len(certificate.ranks), certificate.edge_count, receipt[0], receipt[1], receipt[3],
              receipt[2], packets, maximum, sep=",")
        print("# local minima:", r, local[0], "nonaxis:", local[1], "macro literal edges:", local[2])
    print("exact finite residual certificates:", all_pairs, "disk pairs;", all_packets, "full packet paths")
    require_contract("At r=12,13,15,16,18,20,32 every integer pair in z^2+y^2<r^2 has a checked finite-square rank to the diagonal small box; central and extreme full packets replay literal paths to labelled coincidence. Nonaxis failures of one-step energy descent are exactly the four stated resonant pairs when 3 divides r; the axis and resonant blocks strictly descend in at most three literal edges except at the separately checked unit exit. Forged ranks, ordinals, endpoints and exhausted budgets are refused. No uniform parameter theorem is asserted by this finite replay.")
