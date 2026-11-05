"""Exact finite identities, word-order controls and bounded refusal contract."""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.rat_q import Q
from mojo_smoke.claims import require_contract
from psc.c4_nonunit_residue_occupancy import (
    ResidueTable,
    build_residue_table,
    certify_named_depth_two,
    check_strong_coincidence,
    find_row,
    named_substitution,
    residue_key,
    same_vector,
    verify_conservation,
    verify_named_strong_coincidences,
)


def require_row(table: ResidueTable, letter: Int, key: List[Int], counts: List[Int]) raises:
    var index = find_row(table, letter, key)
    assert_true(index >= 0)
    assert_true(same_vector(table.rows[index].counts, counts))


def test_full_depth_two_table() raises:
    var table = build_residue_table(named_substitution(), 2)
    assert_equal(table.index, 4)
    assert_equal(len(table.rows), 6)
    assert_true(same_vector(table.matrix.e, [1, 3, 1, 1, 3, 3, 1, 1, 1]))
    assert_true(same_vector(table.adjugate.e, [0, -2, 6, 2, 0, -2, -2, 2, 0]))
    assert_true(same_vector(table.words[0], [0, 2, 1]))
    assert_true(same_vector(table.words[1], [1, 0, 0, 1, 0, 2, 1]))
    assert_true(same_vector(table.words[2], [1, 1, 0, 2, 1]))
    require_row(table, 0, [0, 0, 0], [1, 1, 1])
    require_row(table, 0, [2, 0, 2], [0, 1, 0])
    require_row(table, 0, [2, 2, 0], [0, 1, 0])
    require_row(table, 1, [0, 0, 0], [0, 1, 1])
    require_row(table, 1, [2, 0, 2], [1, 2, 2])
    require_row(table, 2, [0, 2, 2], [1, 1, 1])
    # An M^2 column represents zero even when coordinate residues mod 4 do not.
    var column: List[Int] = [1, 1, 1]
    assert_true(same_vector(residue_key(table.adjugate, table.index, column), [0, 0, 0]))
    assert_false(same_vector(column, [0, 0, 0]))


def test_all_depths_conserve_and_certificate() raises:
    var expected_index = 1
    for depth in range(1, 7):
        expected_index *= 2
        var table = build_residue_table(named_substitution(), depth)
        assert_equal(table.index, expected_index)
        verify_conservation(table)
    var certificate = certify_named_depth_two(build_residue_table(named_substitution(), 2))
    assert_true(Q(2, 1).lt(certificate.beta.lo))
    assert_true(certificate.beta.lo.lt(certificate.beta.hi))
    for letter in range(3):
        assert_false(certificate.interval_upper_bounds[letter].rejected)
        assert_true(certificate.interval_upper_bounds[letter].lt(Q(1, 2)))
    assert_true(certificate.exact_third_upper.eq(Q(1, 4)))


def test_word_order_and_unit_controls() raises:
    var reordered = named_substitution()
    reordered[1] = [0, 1, 2]
    var table = build_residue_table(reordered, 2)
    require_row(table, 0, [0, 0, 0], [1, 0, 1])
    var refused = False
    try:
        _ = certify_named_depth_two(table)
    except:
        refused = True
    assert_true(refused)
    var tribonacci = List[List[Int]]()
    tribonacci.append([0, 1])
    tribonacci.append([0, 2])
    tribonacci.append([0])
    for depth in range(1, 7):
        var unit = build_residue_table(tribonacci, depth)
        assert_equal(unit.index, 1)
        for i in range(len(unit.rows)):
            assert_true(same_vector(unit.rows[i].key, [0, 0, 0]))


def test_mutated_certificate_table_refuses() raises:
    var table = build_residue_table(named_substitution(), 2)
    # Moving an unselected row preserves source/letter conservation, but must
    # not be admitted as evidence of the named actual-prefix partition.
    var index = find_row(table, 0, [2, 2, 0])
    table.rows[index].key = [1, 1, 1]
    verify_conservation(table)
    var refused = False
    try:
        _ = certify_named_depth_two(table)
    except:
        refused = True
    assert_true(refused)
    table.rows[index].letter = 3
    refused = False
    try:
        verify_conservation(table)
    except:
        refused = True
    assert_true(refused)


def test_literal_strong_coincidences() raises:
    verify_named_strong_coincidences()
    var images = named_substitution()
    assert_false(check_strong_coincidence(images, 0, 1, 5, 31, [12, 12, 7], 1))
    assert_false(check_strong_coincidence(images, 0, 1, 5, 31, [12, 13, 6], 0))
    assert_false(check_strong_coincidence(images, 0, 1, 1, 31, [12, 13, 6], 1))


def must_refuse(images: List[List[Int]], depth: Int, word_cap: Int, row_cap: Int) raises:
    var refused = False
    try:
        _ = build_residue_table(images, depth, word_cap, row_cap)
    except:
        refused = True
    assert_true(refused)


def test_caps_and_invalid_inputs() raises:
    var images = named_substitution()
    must_refuse(images, -1, 100000, 2187)
    must_refuse(images, 7, 100000, 2187)
    must_refuse(images, 2, 2, 2187)
    must_refuse(images, 2, 100000, 1)
    must_refuse(images, 2, 0, 2187)
    must_refuse(images, 2, 100001, 2187)
    must_refuse(images, 2, 100000, 0)
    must_refuse(images, 2, 100000, 2188)
    var malformed = images.copy()
    malformed[0] = [0, 1, 2, 0]
    must_refuse(malformed, 1, 100000, 2187)
    malformed[0] = [3]
    must_refuse(malformed, 1, 100000, 2187)
    malformed[0] = List[Int]()
    must_refuse(malformed, 1, 100000, 2187)
    var singular = List[List[Int]]()
    singular.append([0])
    singular.append([0])
    singular.append([0])
    must_refuse(singular, 1, 100000, 2187)


def main() raises:
    test_full_depth_two_table()
    test_all_depths_conserve_and_certificate()
    test_word_order_and_unit_controls()
    test_mutated_certificate_table_refuses()
    test_literal_strong_coincidences()
    test_caps_and_invalid_inputs()
    print("[PASS] bounded non-unit residue tables, exact named certificate, controls and SC witnesses")
    require_contract("Three-letter image-length<=3 depth<=6 actual-prefix residue counts; named 1/021/001 depth-two strict-half algebra certificate and literal strong coincidences")
