"""Deterministic complete finite-cylinder records; no strict-density admission."""

from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from psc.c4_finite_cylinder_overlap import (
    GRID, build_certificate, certify_radius, find_strong_coincidence,
    make_chart, pair_area_sum,
)
from psc.exact import q_string, require_q


def main() raises:
    print("schema c4-finite-cylinder-v1")
    for fixture in range(2):
        var images = String("1/021/001") if fixture == 0 else String("1/012/001")
        print("fixture", fixture, images, 2)
        var chart = make_chart()
        certify_radius(fixture, chart)
        print("chart", fixture, q_string(chart.beta.lo), q_string(chart.beta.hi), chart.radius, chart.block, q_string(chart.kappa.lo), q_string(chart.kappa.hi))
        for depth in range(2, 7, 2):
            var certificate = build_certificate(fixture, depth)
            for i in range(len(certificate.occurrences)):
                var row = certificate.occurrences[i].copy()
                print("occurrence", fixture, depth, row.source, row.position, row.letter, row.prefix[0], row.prefix[1], row.prefix[2], row.key[0], row.key[1], row.key[2], row.parent[0], row.parent[1], row.parent[2], q_string(Q(Int64(row.box.xlo), GRID)), q_string(Q(Int64(row.box.xhi), GRID)), q_string(Q(Int64(row.box.ylo), GRID)), q_string(Q(Int64(row.box.yhi), GRID)))
            for i in range(len(certificate.slices)):
                var row = certificate.slices[i].copy()
                print("slice", fixture, depth, row.letter, row.key[0], row.key[1], row.key[2], q_string(Q(Int64(row.box.xlo), GRID)), q_string(Q(Int64(row.box.xhi), GRID)), q_string(Q(Int64(row.box.ylo), GRID)), q_string(Q(Int64(row.box.yhi), GRID)))
            for first in range(3):
                for second in range(first + 1, 3):
                    var area = pair_area_sum(certificate, first, second)
                    var upper = require_q(area.div(q_int(certificate.index)), "normalized output upper")
                    print("upper", fixture, depth, first, second, q_string(area), q_string(upper))
        for first in range(3):
            for second in range(first + 1, 3):
                var witness = find_strong_coincidence(fixture, first, second)
                print("sc", fixture, first, second, witness.depth, witness.position, witness.prefix[0], witness.prefix[1], witness.prefix[2], witness.letter)
        print("status", fixture, "upper_only_no_strict_density")
