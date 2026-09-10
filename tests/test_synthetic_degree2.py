from psc_research.synthetic_degree2 import (
    A,
    B,
    MINUS_G,
    N,
    PLUS_F,
    Q,
    S,
    STATES,
    abstract_endpoint_constraints_hold,
    endpoint_type_pair,
    every_incidence_variant_has_global_endpoint_sync,
    signed_counts_from_words,
    state_k2_matrix,
    state_parikh_matrix,
    states_are_irreducible,
    tribonacci_incidence_variants,
    verify_synthetic_template,
)


def test_synthetic_template_passes_all_claimed_constraints():
    assert verify_synthetic_template()
    assert state_parikh_matrix() == (
        (3, 3, 2),
        (2, 1, 1),
        (1, 1, 0),
    )
    assert state_k2_matrix() == Q
    assert states_are_irreducible()
    assert signed_counts_from_words() == (A, B)


def test_abstract_endpoint_phase_is_nonsynchronizing_and_child_compatible():
    assert PLUS_F == (1, 0, 0)
    assert MINUS_G == (1, 2, 0)
    assert abstract_endpoint_constraints_hold()


def test_same_incidence_has_only_four_actual_word_orderings():
    variants = tribonacci_incidence_variants()
    assert len(variants) == 4
    assert len({tuple(variant[a] for a in (1, 2, 3)) for variant in variants}) == 4


def test_every_actual_ordering_has_a_globally_synchronizing_endpoint_map():
    variants = tribonacci_incidence_variants()
    type_pairs = {endpoint_type_pair(sigma) for sigma in variants}
    assert type_pairs == {
        ((0, 0, 0), (1, 2, 0)),  # A / G
        ((0, 0, 1), (1, 0, 0)),  # B / F
        ((1, 0, 0), (0, 0, 1)),  # F / B
        ((1, 2, 0), (0, 0, 0)),  # G / A
    }
    assert every_incidence_variant_has_global_endpoint_sync()


def test_template_is_not_claimed_as_a_real_bpa_component():
    # The point of the artifact is exactly that the abstract F/G endpoint regime
    # is compatible with the signed child selectors and the individual states,
    # but no substitution ordering with incidence N realizes F/G.
    assert endpoint_type_pair(tribonacci_incidence_variants()[0]) != (PLUS_F, MINUS_G)
    assert len(STATES) == 3
    assert N == (
        (1, 1, 1),
        (1, 0, 0),
        (0, 1, 0),
    )
    assert S == (
        (-1, -1, -1),
        (1, 0, 0),
        (0, -1, 0),
    )
