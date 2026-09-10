from fractions import Fraction

import pytest

from psc_research.defect_intertwiner import exterior_square
from psc_research.intertwiner import substitution_incidence
from psc_research.meanarea_integrality import (
    cubic_coefficients,
    determinant_fraction_free,
    forced_meanarea_solution,
    forced_side_areas_pass_bounds,
    solution_is_integral,
    sylvester_determinant_for_substitution,
    sylvester_matrix,
    sylvester_resultant_formula,
)
from psc_research.synthetic_degree2 import SIGMA, SIGNED_CHILDREN, STATES


def proposed_child_words():
    return tuple(tuple(child for child, _sign in word) for word in SIGNED_CHILDREN)


def test_synthetic_child_order_forces_half_integral_meanarea():
    solution = forced_meanarea_solution(SIGMA, STATES, proposed_child_words())
    assert solution == (
        (Fraction(1, 2), Fraction(-1, 2), Fraction(3, 2)),
        (Fraction(3, 2), Fraction(1, 2), Fraction(3, 2)),
        (Fraction(1, 2), Fraction(1, 2), Fraction(-5, 2)),
    )
    assert not solution_is_integral(solution)
    assert not forced_side_areas_pass_bounds(STATES, solution)


def test_sylvester_determinant_matches_resultant_formula_on_synthetic_pip():
    m = substitution_incidence(SIGMA)
    t, u, d = cubic_coefficients(m)
    assert (t, u, d) == (1, -1, 1)
    op = sylvester_matrix(exterior_square(m), m)
    direct = determinant_fraction_free(op)
    formula = sylvester_resultant_formula(t, u, d)
    assert direct == formula
    assert abs(direct) == 16
    assert sylvester_determinant_for_substitution(SIGMA) == direct


def test_integral_extraction_rejects_half_integral_solution():
    from psc_research.meanarea_integrality import integral_solution

    solution = forced_meanarea_solution(SIGMA, STATES, proposed_child_words())
    with pytest.raises(ValueError, match="not integral"):
        integral_solution(solution)


def test_sylvester_operator_is_nonsingular_for_synthetic_pip():
    assert sylvester_determinant_for_substitution(SIGMA) != 0
