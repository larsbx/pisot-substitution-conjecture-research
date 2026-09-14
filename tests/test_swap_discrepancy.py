import pytest

from psc_research.bpa import apply_substitution_n, build_bpa, decompose_pair, seed_states
from psc_research.examples import EXAMPLES
from psc_research.swap_discrepancy import (
    discrepancy,
    max_reachable_discrepancy,
    swap_walk_profile,
    swap_walk_sup,
)

TAU = {1: (2,), 2: (1, 3, 2), 3: (1, 1, 2)}


def test_discrepancy_of_swap_seed_is_one():
    assert discrepancy(((1, 2), (2, 1)), 3) == 1


@pytest.mark.parametrize(
    "state",
    [
        ((0,), (0,)),
        ((4,), (4,)),
        ((0,), (1,)),
        ((1,), (4,)),
    ],
)
def test_discrepancy_rejects_labels_outside_alphabet(state):
    with pytest.raises(ValueError, match=r"outside 1\.\.3"):
        discrepancy(state, 3)


def test_level_zero_swap_walk_is_the_seed():
    assert swap_walk_sup(EXAMPLES["tribonacci"], 1, 2, 0) == 1


def test_blocks_of_inflated_seed_inherit_the_swap_walk_bound():
    # The reduction step of the bounded-discrepancy theorem: every block of
    # red(sigma^n(ab), sigma^n(ba)) has discrepancy at most the swap-walk sup.
    for sigma in (EXAMPLES["tribonacci"], EXAMPLES["flipped_tribonacci"], TAU):
        for (a, b), _ in seed_states(3):
            for n in range(0, 9):
                u = apply_substitution_n(sigma, (a, b), n)
                v = apply_substitution_n(sigma, (b, a), n)
                sup = swap_walk_sup(sigma, a, b, n)
                assert all(discrepancy(block, 3) <= sup for block in decompose_pair(u, v, 3))


def test_reachable_discrepancy_matches_exact_census_values():
    assert max_reachable_discrepancy(build_bpa(EXAMPLES["tribonacci"]), 3) == 1
    assert max_reachable_discrepancy(build_bpa(TAU), 3) == 5


def test_swap_walk_profile_is_flat_on_tribonacci():
    assert set(swap_walk_profile(EXAMPLES["tribonacci"], range(0, 16)).values()) == {1}
