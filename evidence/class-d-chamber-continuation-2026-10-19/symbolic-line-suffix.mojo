"""Run tests hidden behind the inherited q0=18 assertion, without waiving it."""
from tests.test_symbolic_line import (
    test_two_parameter_polynomials_and_quadrant_signs,
    test_every_wedge_edge_is_a_pinned_line,
    test_norm_mode_shrinks_a_threshold_near_the_asymptote,
    test_the_norm_is_the_product_over_the_roots,
)

def main() raises:
    test_two_parameter_polynomials_and_quadrant_signs()
    print("PASS two_parameter_polynomials_and_quadrant_signs")
    test_every_wedge_edge_is_a_pinned_line()
    print("PASS every_wedge_edge_is_a_pinned_line")
    test_norm_mode_shrinks_a_threshold_near_the_asymptote()
    print("PASS norm_mode_shrinks_a_threshold_near_the_asymptote")
    test_the_norm_is_the_product_over_the_roots()
    print("PASS norm_is_the_product_over_the_roots")
    print("SYMBOLIC_LINE_SUFFIX_PASSED; full regression still fails at q0 pin")
