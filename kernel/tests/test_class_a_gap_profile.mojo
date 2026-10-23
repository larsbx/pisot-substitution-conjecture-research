"""Residue profiles of exact class-A graphs agree with every tabulated ray's carrier cardinality."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_line_graph import residue_profile
from psc.class_a_ray_tables import tabulated_rays


def main() raises:
    var rays = tabulated_rays()
    for d in range(2, 5):
        for eps in [1, -1]:
            # Compare from the line's largest floor: below it the certificate does not speak.
            var floor = 0
            for spec in rays:
                if spec[0] == d and spec[1] == eps:
                    floor = max(floor, spec[3])
            var profile = residue_profile(d, eps, 40, (floor + d - 1) // d)
            assert_equal(len(profile), d)
            for spec in rays:
                if spec[0] != d or spec[1] != eps:
                    continue
                var row = profile[spec[2]].copy()
                assert_equal(row[0], spec[2])
                assert_equal(row[4], 1)                      # affine on every member from the floor
                assert_equal(row[1], spec[4])                # slope of the proved cardinality
                assert_equal(row[2], spec[5])                # its constant
    # A residue of a line with no member at l >= 2 within the budget is omitted, not guessed.
    assert_true(len(residue_profile(16, 1, 20)) < 16)
    require_contract("class-A residue profiles: on every tabulated ray with d<=4 the exact complete-graph vertex counts for n<=40 are affine in l from the line's largest floor and equal the ray's proved carrier cardinality; residues without two members at l>=2 are omitted; finite observation, not uniform in d")
