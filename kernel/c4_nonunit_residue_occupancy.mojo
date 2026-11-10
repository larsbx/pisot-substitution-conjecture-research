"""Deterministic full-table replay for the named non-unit certificate."""

from psc.c4_nonunit_residue_occupancy import (
    build_residue_table,
    certify_named_depth_two,
    named_substitution,
    verify_named_strong_coincidences,
)
from psc.exact import q_string


def main() raises:
    print("scope alphabet=3 image_length=1..3 depth=1..6 word_cap=100000 row_cap=2187")
    print("specimen 1/021/001; rows are actual strict-prefix classes in Z^3/M^q Z^3")
    var images = named_substitution()
    for depth in range(1, 7):
        var table = build_residue_table(images, depth)
        print("table", depth, "index", table.index, "rows", len(table.rows))
        for i in range(len(table.rows)):
            var row = table.rows[i].copy()
            print("row", depth, row.letter, row.key[0], row.key[1], row.key[2], row.counts[0], row.counts[1], row.counts[2])
        if depth == 2:
            var certificate = certify_named_depth_two(table)
            print("beta_bracket", q_string(certificate.beta.lo), q_string(certificate.beta.hi))
            for letter in range(3):
                print("interval_upper", letter, q_string(certificate.interval_upper_bounds[letter]))
            print("exact_upper 0 (beta+2)/(4*beta)")
            print("exact_upper 1 beta^4/(4*(2*beta^2+3*beta+2))")
            print("exact_upper 2", q_string(certificate.exact_third_upper))
            print("certificate all_three_strictly_below_one_half")
    verify_named_strong_coincidences()
    print("strong_coincidence 1 2 1 0 0 0 0 0")
    print("strong_coincidence 0 1 5 31 12 13 6 1")
    print("strong_coincidence 0 2 6 31 12 13 6 1")
    print("scope finite residue/word/algebra certificate; measure implication is documented separately")
