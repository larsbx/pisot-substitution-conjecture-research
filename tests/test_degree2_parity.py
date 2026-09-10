from psc_research.degree2_parity import (
    characteristic_cubic_mod2,
    exterior_characteristic_cubic_mod2,
    gcd_mod2,
    minimum_degree2_scc_size_from_parity,
    parity_sieve,
)


def test_all_eight_parity_classes_have_expected_lower_bound():
    expected = {
        (0, 0, 0): 3,
        (0, 0, 1): 3,
        (0, 1, 0): 4,
        (0, 1, 1): 6,
        (1, 0, 0): 4,
        (1, 0, 1): 6,
        (1, 1, 0): 5,
        (1, 1, 1): 3,
    }
    for parity, bound in expected.items():
        assert minimum_degree2_scc_size_from_parity(*parity) == bound


def test_odd_determinant_opposite_trace_second_parities_are_coprime():
    for trace, second in ((0, 1), (1, 0)):
        data = parity_sieve(trace, second, 1)
        assert data.gcd_mod2 == 1
        assert data.lcm_degree == 6


def test_three_state_degree2_case_requires_reduced_cubics_to_coincide():
    allowed = []
    for trace in (0, 1):
        for second in (0, 1):
            for det in (0, 1):
                p = characteristic_cubic_mod2(trace, second, det)
                q = exterior_characteristic_cubic_mod2(trace, second, det)
                if minimum_degree2_scc_size_from_parity(trace, second, det) == 3:
                    assert p == q
                    allowed.append((trace, second, det))
    assert allowed == [(0, 0, 0), (0, 0, 1), (1, 1, 1)]


def test_polynomial_gcd_examples():
    # t^3+t+1 and t^3+t^2+1 are coprime over F2.
    p = characteristic_cubic_mod2(0, 1, 1)
    q = exterior_characteristic_cubic_mod2(0, 1, 1)
    assert gcd_mod2(p, q) == 1

    # For (T,U,d)=(1,1,0), gcd is t.
    p = characteristic_cubic_mod2(1, 1, 0)
    q = exterior_characteristic_cubic_mod2(1, 1, 0)
    assert gcd_mod2(p, q) == 0b10
