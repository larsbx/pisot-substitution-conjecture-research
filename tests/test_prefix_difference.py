from psc_research.bpa import build_bpa, coincidence_boundaries
from psc_research.examples import EXAMPLES
from psc_research.prefix_difference import (
    component_block_bound,
    image_prefix_lengths,
    inflated_prefix_lift,
    possible_local_corrections,
    source_offset_bound_from_corrections,
    strict_child_closed,
    verify_uniform_return_gap,
    zero_return_lifts,
)


NON_PISOT_STRICT = {1: (2,), 2: (1, 2, 3), 3: (2,)}
STRICT_COMPONENT = (
    ((1, 2), (2, 1)),
    ((2, 3), (3, 2)),
)


def test_exact_inflation_identity_on_named_bpa_states_and_all_output_cuts():
    for sigma in EXAMPLES.values():
        graph = build_bpa(sigma, max_states=2500)
        # This test is about the exact local identity, not exhaustive census
        # coverage.  A deterministic prefix of the sorted state set exercises
        # many different image-length and source-index misalignments cheaply.
        for state in sorted(graph)[:40]:
            u, v = state
            total = sum(len(sigma[a]) for a in u)
            assert total == sum(len(sigma[a]) for a in v)
            for cut in range(total + 1):
                lift = inflated_prefix_lift(sigma, state, cut)
                assert sum(lift.source_difference) == lift.source_index_offset


def test_zero_return_ancestry_uses_finite_local_correction_alphabet():
    for sigma in EXAMPLES.values():
        correction_alphabet = set(possible_local_corrections(sigma))
        offset_bound = source_offset_bound_from_corrections(sigma)
        graph = build_bpa(sigma, max_states=2500)
        for state in sorted(graph)[:80]:
            for lift in zero_return_lifts(sigma, state):
                assert lift.is_zero_return
                assert lift.local_difference in correction_alphabet
                assert abs(lift.source_index_offset) <= offset_bound
                assert sum(lift.source_difference) == lift.source_index_offset


def test_old_zero_return_boundary_lifts_to_aligned_source_boundary():
    sigma = EXAMPLES["smith"]
    graph = build_bpa(sigma, max_states=2500)
    for state in sorted(graph)[:80]:
        u, v = state
        upos = image_prefix_lengths(sigma, u)
        vpos = image_prefix_lengths(sigma, v)
        for source_cut in coincidence_boundaries(u, v, 3):
            assert upos[source_cut] == vpos[source_cut]
            lift = inflated_prefix_lift(sigma, state, upos[source_cut])
            assert lift.top_source_index == source_cut
            assert lift.bottom_source_index == source_cut
            assert lift.top_offset == 0
            assert lift.bottom_offset == 0
            assert lift.source_difference == (0, 0, 0)
            assert lift.local_difference == (0, 0, 0)
            assert lift.is_zero_return


def test_nonpisot_negative_control_is_strict_child_closed():
    assert strict_child_closed(NON_PISOT_STRICT, STRICT_COMPONENT)
    assert component_block_bound(STRICT_COMPONENT) == 2


def test_strict_component_has_uniform_zero_return_gap_across_iterates():
    # The theorem is not Pisot-specific.  This negative-control component is
    # genuinely closed and nonproductive, so it is a good calibration that
    # dense zero returns alone do not prove C4.
    assert verify_uniform_return_gap(NON_PISOT_STRICT, STRICT_COMPONENT, max_depth=6)
