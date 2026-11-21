"""Bounded independent replays of the unbounded companion-family witness.

The declared parameter domain is every even r in 2..32 plus the odd r=3
boundary. PIP and eventual-range predicates use the existing exact kernels.
The literal search independently checks the proposed witness, while the
finite runs are not the proof of the statement for all r.
"""

from std.testing import assert_equal, assert_true
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.bpa import substitution_incidence
from psc.c4_cut_attractor import left_witness
from psc.c4_geometric_f import chi_mod2_code, principal_minor_sum
from psc.even_companion_family import (
    companion_family,
    literal_iterate,
    uniform_prefixes,
    verify_uniform_witness,
)
from psc.h1_census import eventual_range, h1_profile, legal_two_words
from psc.pisot import is_pip
from psc.words import parikh

comptime WORD_CAP = 100000


def test_even_parameter_domain() raises:
    var count = 0
    for r in range(2, 33, 2):
        var sigma = companion_family(r)
        var m = Mat3(substitution_incidence(sigma))
        assert_true(is_pip(m))
        assert_equal(m.charpoly(), [-2, -2, -r, 1])
        assert_equal(m.det(), 2)
        assert_equal(chi_mod2_code(m.det(), m.trace(), principal_minor_sum(m)), 0)
        assert_equal(
            eventual_range(sigma, legal_two_words(sigma)),
            [False, False, False, False, True, True, False, True, True],
        )
        assert_equal(h1_profile(sigma).dimension, 4)
        # sigma(0)=1 and sigma(2) starts with 1, at empty prefixes.
        assert_equal(left_witness(sigma, 0, 2, 1, WORD_CAP), [1, 0, 1])
        if r >= 3:
            var expected: List[Int] = [3, r + 12, 2]
            assert_equal(verify_uniform_witness(r, WORD_CAP), expected)
            assert_equal(left_witness(sigma, 1, 2, 3, WORD_CAP), expected)
            # sigma^4(0)=sigma^3(1), sigma^4(1)=sigma^3(2).
            assert_equal(left_witness(sigma, 0, 1, 4, WORD_CAP), [4, r + 12, 2])
            if r == 4:
                assert_equal(expected, [3, 16, 2])
                assert_equal(parikh(uniform_prefixes(r)[0]), [4, 5, 7])
        else:
            # r=2 is not covered by the uniform level-three formula.
            assert_equal(left_witness(sigma, 1, 2, 3, WORD_CAP), [-1, -1, -1])
            assert_equal(left_witness(sigma, 1, 2, 4, WORD_CAP), [4, 20, 2])
            assert_equal(left_witness(sigma, 0, 1, 5, WORD_CAP), [5, 20, 2])
            for a in range(1, 3):
                var word = literal_iterate(sigma, a, 4, WORD_CAP)
                assert_equal(word[20], 2)
                assert_equal(parikh([word[i] for i in range(20)]), [6, 7, 7])
            var top = literal_iterate(sigma, 1, 3, WORD_CAP)
            var bottom = literal_iterate(sigma, 2, 3, WORD_CAP)
            assert_equal(top[14], 1)
            assert_equal(bottom[14], 2)
        count += 1
    assert_equal(count, 16)
    print("EVEN_COMPANION_FAMILY", "even_r=2..32", "specimens", count,
          "nilpotent_mod2=true", "ER=K2,2", "dim_H1=4",
          "all_letter_pairs", 3 * count, "pair02_level=1",
          "r>=4_pair12=level3,offset_r+12,letter2", "r>=4_pair01_level=4",
          "r2_pair12=level4,offset20,letter2", "r2_pair01_level=5")


def test_scope_and_refusal() raises:
    var odd = companion_family(3)
    var m = Mat3(substitution_incidence(odd))
    assert_true(is_pip(m))
    assert_true(chi_mod2_code(m.det(), m.trace(), principal_minor_sum(m)) != 0)
    assert_equal(verify_uniform_witness(3, WORD_CAP), [3, 15, 2])
    assert_equal(left_witness(odd, 0, 2, 1, WORD_CAP), [1, 0, 1])
    assert_equal(left_witness(odd, 0, 1, 4, WORD_CAP), [4, 15, 2])
    var refused = False
    try:
        _ = uniform_prefixes(2)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = companion_family(0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = companion_family(32, 35)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = verify_uniform_witness(4, 10)
    except:
        refused = True
    assert_true(refused)
    print("EVEN_COMPANION_FAMILY_CONTROLS", "r3_odd=true", "r2_formula_refused=true",
          "invalid_parameter_refused=true", "image_cap_refused=true", "word_cap_refused=true")


def main() raises:
    test_even_parameter_domain()
    test_scope_and_refusal()
    require_contract("Even companion family: every even r in 2..32 has exact cubic Pisot incidence, nilpotent reduction modulo two, and K2,2 eventual range. All 48 unordered letter pairs have literal strong-coincidence witnesses: for r>=4 the levels for pairs 02,12,01 are 1,3,4; r=2 has levels 1,4,5. The explicit periodic-letter prefix witness agrees with independent literal search. Odd r=3 validates the word formula without nilpotent parity, and exhausted budgets refuse to conclude. The finite replay is separate from the unbounded Lean theorem.")
