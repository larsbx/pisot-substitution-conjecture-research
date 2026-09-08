from psc_research import apply_substitution, coincidence_boundaries, decompose_pair, parikh


def test_parikh():
    assert parikh((1, 2, 1, 3), 3) == (2, 1, 1)


def test_apply_substitution():
    sigma = {1: (2, 1), 2: (3, 1), 3: (1,)}
    assert apply_substitution(sigma, (1, 2)) == (2, 1, 3, 1)


def test_flipped_tribonacci_decomposition_has_coincidence_sibling():
    sigma_u = (2, 1, 3, 1)
    sigma_v = (3, 1, 2, 1)
    assert coincidence_boundaries(sigma_u, sigma_v, 3) == [0, 3, 4]
    assert decompose_pair(sigma_u, sigma_v, 3) == [((2, 1, 3), (3, 1, 2)), ((1,), (1,))]
