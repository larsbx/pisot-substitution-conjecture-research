"""Independent Python oracle for the census of irreducible distinct binomially
equivalent pairs (docs/c4-binomial-minimal-pairs-2026-11-07.md).

The canonical census is kernel/binomial_pair_census.mojo (kernel/psc/binomial_pairs.mojo),
pinned by kernel/tests/test_binomial_pair_census.mojo. This test runs the
stdlib oracle oracles/python/binomial_pair_census.py, which shares no code with
it, on d = 3, n <= 9 and d = 2, n <= 14, and checks it against the same table.
"""
import runpy
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
ORACLE = runpy.run_path(str(ROOT / "oracles/python/binomial_pair_census.py"))

# n: (irreducible unordered, degree 2, 3, 4, 5+), from the Mojo census table
TERNARY = {
    1: (0, 0, 0, 0, 0),
    2: (3, 3, 0, 0, 0),
    3: (15, 15, 0, 0, 0),
    4: (90, 90, 0, 0, 0),
    5: (594, 594, 0, 0, 0),
    6: (4161, 4161, 0, 0, 0),
    7: (30357, 30351, 6, 0, 0),
    8: (228087, 228063, 24, 0, 0),
    9: (1752315, 1752117, 198, 0, 0),
}
BINARY = {
    1: (0, 0, 0, 0, 0),
    2: (1, 1, 0, 0, 0),
    3: (2, 2, 0, 0, 0),
    4: (5, 5, 0, 0, 0),
    5: (14, 14, 0, 0, 0),
    6: (42, 42, 0, 0, 0),
    7: (132, 132, 0, 0, 0),
    8: (429, 429, 0, 0, 0),
    9: (1430, 1430, 0, 0, 0),
    10: (4862, 4862, 0, 0, 0),
    11: (16796, 16796, 0, 0, 0),
    12: (58786, 58786, 0, 0, 0),
    13: (208012, 208012, 0, 0, 0),
    14: (742900, 742900, 0, 0, 0),
}
# n: (classes N2, N3, N4), from the Mojo census table
TERNARY_CLASSES = {4: (78, 81, 81), 7: (1410, 2181, 2187), 8: (3309, 6522, 6561)}
BINARY_CLASSES = {7: (64, 126, 128), 8: (93, 247, 256), 12: (299, 3337, 4092)}
# Chrisnata et al., ISCIT 2019, Table I: D_3(n), D_4(n)
TABLE_I = {7: (126, 128), 8: (247, 256), 12: (3337, 4092)}

SEEDS_1_BASED = [
    ("1223312", "2311223"), ("1233112", "3112231"), ("1322113", "2113321"),
    ("1332213", "3211332"), ("2133221", "3221132"), ("2331123", "3122331"),
]


def word(s, shift=0):
    return tuple(int(c) - shift for c in s)


def counts(row):
    return (row["total"], row["degree2"], row["degree3"], row["degree4"], row["degree5plus"])


@pytest.mark.parametrize("d, table", [(3, TERNARY), (2, BINARY)])
def test_counts_match_the_mojo_table(d, table):
    for n, expected in table.items():
        assert counts(ORACLE["census"](n, d, classes=False)) == expected, (d, n)


def test_renewal_total_matches_brute_force():
    renewal3 = ORACLE["irreducible_ordered"](6, 3)
    for n in range(1, 7):
        assert renewal3[n] == ORACLE["brute_irreducible_ordered"](n, 3)
    renewal2 = ORACLE["irreducible_ordered"](10, 2)
    for n in range(1, 11):
        assert renewal2[n] == ORACLE["brute_irreducible_ordered"](n, 2)


def test_binary_closed_form():
    renewal = ORACLE["irreducible_ordered"](20, 2)
    for n in range(2, 21):
        assert renewal[n] == 2 * ORACLE["catalan"](n - 1)


def test_class_counts_and_table_i():
    for n, expected in TERNARY_CLASSES.items():
        row = ORACLE["census"](n, 3)
        assert (row["classes2"], row["classes3"], row["classes4"]) == expected
    for n, expected in BINARY_CLASSES.items():
        row = ORACLE["census"](n, 2)
        assert (row["classes2"], row["classes3"], row["classes4"]) == expected
        assert (row["classes3"], row["classes4"]) == TABLE_I[n]


def test_length_seven_list_is_the_six_seeds():
    row = ORACLE["census"](7, 3, classes=False)
    listed = {(u, v) for u, v, _ in row["pairs"]}
    seeds = {tuple(sorted((word(u, 1), word(v, 1)))) for u, v in SEEDS_1_BASED}
    assert listed == seeds
    assert all(deg == 3 for _, _, deg in row["pairs"])
    assert (word("0112201"), word("1200112")) in listed


def test_negative_controls():
    irr = ORACLE["is_irreducible"]
    deg = ORACLE["first_defect_degree"]
    # Thue-Morse blocks: degree k + 1, irreducible only for k = 1
    blocks = {1: ("01", "10"), 2: ("0110", "1001"), 3: ("01101001", "10010110")}
    for k, (u, v) in blocks.items():
        assert deg(word(u), word(v)) == k + 1
        assert irr(word(u), word(v), 2) == (k == 1)
    # S(3) witness and a commutation pair, both reducible
    assert deg(word("0110001"), word("1000110")) == 4
    assert not irr(word("0110001"), word("1000110"), 2)
    assert deg(word("012120"), word("120012")) == 3
    assert not irr(word("012120"), word("120012"), 3)
    # a K2 != 0 pair is never listed: (01, 10) is irreducible of degree 2
    row = ORACLE["census"](2, 3, classes=False)
    assert row["pairs"] == [] and row["degree2"] == 3
