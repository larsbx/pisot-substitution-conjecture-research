"""Regression test of the census of irreducible distinct binomially equivalent pairs.

Pins the full table of `kernel/binomial_pair_census.mojo` on the gate's window
(`docs/c4-solidify-stop-go-2026-11-07.md` §3.6; ternary `n <= 12`, binary
`n <= 20`), reported in `docs/c4-binomial-minimal-pairs-2026-11-07.md`. Any
change of a pinned count fails. Also pinned: the lattice-walk total against
brute force, the prefix-code irreducibility test against
`psc.bpa.coincidence_boundaries`, the stable row sort, the four scratch items
of §3.6 ((i)-(iii) on the window, and (iv) at `n = 13`; the `n = 14` row is
the driver's extension run, recorded in the docs note, and is not pinned
here), the controls of §3.5, and the fail-closed refusals.

Replay (from `kernel/`):
    pixi run --locked mojo run -I . -I tests tests/test_binomial_pair_census.mojo
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.binomial_pairs import (
    LengthCensus,
    binary_closed_form_ordered,
    brute_irreducible_ordered_pairs,
    catalan,
    census_length,
    census_window,
    class_words,
    codes_irreducible,
    contains_pair,
    digits,
    g_canonical,
    g_representatives,
    irreducible_ordered_pairs,
    is_irreducible_pair,
    minimal_length,
    orbit_representatives,
    parikh_vectors,
    prefix_codes,
    scattered_count,
    sorted_row_order,
    table_i_d3,
    table_i_d4,
    thue_morse_block,
    word_at,
)
from psc.bpa import coincidence_boundaries
from psc.defect_degree import DEGREE_FIVE_PLUS, DEGREE_FOUR, DEGREE_THREE, DEGREE_TWO, first_defect_degree, n4
from psc.seeds import length7_seeds
from psc.words import Pair, is_zero, k2, k3, n2, n3

comptime COLUMNS = 13


def pinned_binary() -> List[Int]:
    """Columns: n, words, classes N2, N3, N4, irreducible unordered, degree 2, 3, 4, 5+,
    G-classes of degree 3, 4, 5+ -- binary, n = 1 .. 20."""
    var t: List[Int] = [
        1, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0,
        2, 4, 4, 4, 4, 1, 1, 0, 0, 0, 0, 0, 0,
        3, 8, 8, 8, 8, 2, 2, 0, 0, 0, 0, 0, 0,
        4, 16, 15, 16, 16, 5, 5, 0, 0, 0, 0, 0, 0,
        5, 32, 26, 32, 32, 14, 14, 0, 0, 0, 0, 0, 0,
        6, 64, 42, 64, 64, 42, 42, 0, 0, 0, 0, 0, 0,
        7, 128, 64, 126, 128, 132, 132, 0, 0, 0, 0, 0, 0,
        8, 256, 93, 247, 256, 429, 429, 0, 0, 0, 0, 0, 0,
        9, 512, 130, 480, 512, 1430, 1430, 0, 0, 0, 0, 0, 0,
        10, 1024, 176, 926, 1024, 4862, 4862, 0, 0, 0, 0, 0, 0,
        11, 2048, 232, 1764, 2048, 16796, 16796, 0, 0, 0, 0, 0, 0,
        12, 4096, 299, 3337, 4092, 58786, 58786, 0, 0, 0, 0, 0, 0,
        13, 8192, 378, 6208, 8176, 208012, 208012, 0, 0, 0, 0, 0, 0,
        14, 16384, 470, 11408, 16328, 742900, 742900, 0, 0, 0, 0, 0, 0,
        15, 32768, 576, 20608, 32604, 2674440, 2674440, 0, 0, 0, 0, 0, 0,
        16, 65536, 697, 36649, 65075, 9694845, 9694845, 0, 0, 0, 0, 0, 0,
        17, 131072, 834, 63976, 129824, 35357670, 35357670, 0, 0, 0, 0, 0, 0,
        18, 262144, 988, 109866, 258906, 129644790, 129644790, 0, 0, 0, 0, 0, 0,
        19, 524288, 1160, 185012, 516168, 477638700, 477638700, 0, 0, 0, 0, 0, 0,
        20, 1048576, 1351, 306285, 1028448, 1767263190, 1767263190, 0, 0, 0, 0, 0, 0,
    ]
    return t^


def pinned_ternary() -> List[Int]:
    """The same columns, ternary, n = 1 .. 12."""
    var t: List[Int] = [
        1, 3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0,
        2, 9, 9, 9, 9, 3, 3, 0, 0, 0, 0, 0, 0,
        3, 27, 27, 27, 27, 15, 15, 0, 0, 0, 0, 0, 0,
        4, 81, 78, 81, 81, 90, 90, 0, 0, 0, 0, 0, 0,
        5, 243, 216, 243, 243, 594, 594, 0, 0, 0, 0, 0, 0,
        6, 729, 568, 729, 729, 4161, 4161, 0, 0, 0, 0, 0, 0,
        7, 2187, 1410, 2181, 2187, 30357, 30351, 6, 0, 0, 1, 0, 0,
        8, 6561, 3309, 6522, 6561, 228087, 228063, 24, 0, 0, 2, 0, 0,
        9, 19683, 7307, 19482, 19683, 1752315, 1752117, 198, 0, 0, 19, 0, 0,
        10, 59049, 15303, 58152, 59049, 13699053, 13697823, 1230, 0, 0, 105, 0, 0,
        11, 177147, 30435, 173340, 177147, 108604737, 108597093, 7644, 0, 0, 662, 0, 0,
        12, 531441, 57882, 516279, 531429, 870958746, 870908340, 50394, 12, 0, 4215, 1, 0,
    ]
    return t^


def row_of(c: LengthCensus) raises -> List[Int]:
    var out: List[Int] = [
        c.n, c.words, c.classes2, c.classes3, c.classes4, c.total,
        c.count(DEGREE_TWO), c.count(DEGREE_THREE), c.count(DEGREE_FOUR), c.count(DEGREE_FIVE_PLUS),
        len(g_representatives(c.pairs_of_degree(DEGREE_THREE))),
        len(g_representatives(c.pairs_of_degree(DEGREE_FOUR))),
        len(g_representatives(c.pairs_of_degree(DEGREE_FIVE_PLUS))),
    ]
    return out^


def assert_table(rows: List[LengthCensus], pinned: List[Int]) raises:
    assert_equal(len(rows) * COLUMNS, len(pinned))
    for r in range(len(rows)):
        var got = row_of(rows[r])
        for t in range(COLUMNS):
            if got[t] != pinned[r * COLUMNS + t]:
                raise Error("pinned census table changed: d = " + String(rows[r].alphabet) + ", n = " + String(rows[r].n) + ", column " + String(t) + ": " + String(got[t]) + " != " + String(pinned[r * COLUMNS + t]))
        # the ordered total is twice the unordered one
        assert_equal(rows[r].irreducible_ordered, 2 * rows[r].total)


def test_recurrence_against_brute_force() raises:
    for n in range(1, 8):
        assert_equal(irreducible_ordered_pairs(3, n), brute_irreducible_ordered_pairs(3, n))
    for n in range(1, 13):
        assert_equal(irreducible_ordered_pairs(2, n), brute_irreducible_ordered_pairs(2, n))


def test_closed_form_and_catalan() raises:
    var cat: List[Int] = [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]
    for m in range(len(cat)):
        assert_equal(catalan(m), cat[m])
    for n in range(2, 21):
        assert_equal(irreducible_ordered_pairs(2, n), binary_closed_form_ordered(n))


def test_word_enumeration() raises:
    # the classes of one length partition the alphabet^n words, each word once
    var vectors = parikh_vectors(3, 5)
    assert_equal(len(vectors), 21)
    var total = 0
    for i in range(len(vectors)):
        var words = class_words(vectors[i])
        var m = len(words) // 5
        total += m
        for j in range(1, m):
            var a = word_at(words, 5, j - 1)
            var b = word_at(words, 5, j)
            var less = False
            for t in range(5):
                if a[t] != b[t]:
                    less = a[t] < b[t]
                    break
            assert_true(less)
    assert_equal(total, 243)
    assert_equal(len(parikh_vectors(2, 5)), 6)


def test_prefix_codes_against_library() raises:
    for n in range(2, 7):
        var vectors = parikh_vectors(3, n)
        for pv in range(len(vectors)):
            var words = class_words(vectors[pv])
            var m = len(words) // n
            var codes = prefix_codes(words, n)
            for i in range(m):
                for j in range(m):
                    if i == j:
                        continue
                    var p = Pair(word_at(words, n, i), word_at(words, n, j))
                    assert_equal(codes_irreducible(codes, n, i, j), is_irreducible_pair(p))


def test_sorted_row_order() raises:
    # rows (width 2): [3,1], [1,2], [3,1], [1,1], [2,9]
    var rows: List[Int] = [3, 1, 1, 2, 3, 1, 1, 1, 2, 9]
    var order = sorted_row_order(rows, 2)
    var expected: List[Int] = [3, 1, 4, 0, 2]
    assert_equal(len(order), 5)
    for i in range(5):
        assert_equal(order[i], expected[i])
    var ragged: List[Int] = [1, 2, 3]
    var refused = False
    try:
        _ = sorted_row_order(ragged, 2)
    except:
        refused = True
    assert_true(refused)


def test_scattered_count_matches_kernels() raises:
    var w = digits("0120211020")
    var r2 = n2(w)
    var r3 = n3(w)
    var r4 = n4(w)
    for a in range(3):
        for b in range(3):
            var x2: List[Int] = [a, b]
            assert_equal(scattered_count(w, x2), r2[3 * a + b])
            for c in range(3):
                var x3: List[Int] = [a, b, c]
                assert_equal(scattered_count(w, x3), r3[9 * a + 3 * b + c])
                for d in range(3):
                    var x4: List[Int] = [a, b, c, d]
                    assert_equal(scattered_count(w, x4), r4[27 * a + 9 * b + 3 * c + d])


def test_full_table(binary: List[LengthCensus], ternary: List[LengthCensus]) raises:
    assert_table(binary, pinned_binary())
    assert_table(ternary, pinned_ternary())
    # calibration (gate §3.3): Table I of Chrisnata et al., read through the deck lemma
    var d3 = table_i_d3()
    var d4 = table_i_d4()
    for r in range(len(binary)):
        var n = binary[r].n
        if n >= 3:
            assert_equal(binary[r].classes3, d3[n - 3])
        if n >= 4:
            assert_equal(binary[r].classes4, d4[n - 4])
        assert_equal(binary[r].k2_zero(), 0)
    # minimal lengths in the window
    assert_equal(minimal_length(ternary, DEGREE_TWO), 2)
    assert_equal(minimal_length(ternary, DEGREE_THREE), 7)
    assert_equal(minimal_length(ternary, DEGREE_FOUR), 12)
    assert_equal(minimal_length(ternary, DEGREE_FIVE_PLUS), 0)
    assert_equal(minimal_length(binary, DEGREE_THREE), 0)


def test_items(ternary: List[LengthCensus]) raises:
    # (ii): the length-7 K2 = 0 list is exactly the six seeds, one orbit
    ref r7 = ternary[6]
    assert_equal(r7.n, 7)
    var listed = r7.pairs_of_degree(DEGREE_THREE)
    assert_equal(r7.k2_zero(), 6)
    assert_equal(len(listed), 6)
    var seeds = length7_seeds()
    for i in range(len(seeds)):
        assert_true(contains_pair(listed, seeds[i]))
    assert_equal(len(orbit_representatives(listed, False)), 1)
    assert_equal(len(g_representatives(listed)), 1)
    assert_true(contains_pair(listed, Pair(digits("0112201"), digits("1200112"))))
    # (iii): twelve ~3 pairs at n = 12, all with K4 != 0, one orbit of twelve
    ref r12 = ternary[11]
    assert_equal(r12.n, 12)
    var four = r12.pairs_of_degree(DEGREE_FOUR)
    assert_equal(len(four), 12)
    assert_equal(r12.count(DEGREE_FIVE_PLUS), 0)
    assert_equal(len(orbit_representatives(four, False)), 2)
    var reps = g_representatives(four)
    assert_equal(len(reps), 1)
    var w4 = Pair(digits("011220100112"), digits("120010112201"))
    assert_true(reps[0] == w4)
    assert_true(contains_pair(four, w4))
    for i in range(len(four)):
        assert_true(is_irreducible_pair(four[i]))
        assert_true(is_zero(k2(four[i])) and is_zero(k3(four[i])))
        assert_true(g_canonical(four[i]) == w4)


def test_extension_n13() raises:
    """Gate item (iv) at n = 13 (degree-3 pairs counted, not kept): 24 ~3
    pairs, none ~4, in three G-orbits of sizes 12, 6, 6. The n = 14 row (6
    pairs, one orbit) is the driver's extension run, recorded in the docs note."""
    var c = census_length(3, 13, DEGREE_FOUR)
    var expected: List[Int] = [1594323, 105468, 1535652, 1594251, 7052051538, 7051728264, 323250, 24, 0]
    var got: List[Int] = [c.words, c.classes2, c.classes3, c.classes4, c.total, c.count(DEGREE_TWO), c.count(DEGREE_THREE), c.count(DEGREE_FOUR), c.count(DEGREE_FIVE_PLUS)]
    for t in range(len(expected)):
        if got[t] != expected[t]:
            raise Error("pinned n = 13 row changed at column " + String(t) + ": " + String(got[t]) + " != " + String(expected[t]))
    var four = c.pairs_of_degree(DEGREE_FOUR)
    var reps = g_representatives(four)
    var keys: List[String] = ["0012220001102|2000110222001", "0112201110021|1200111022110", "0112202110021|1200112022110"]
    var sizes: List[Int] = [12, 6, 6]
    assert_equal(len(reps), 3)
    for r in range(3):
        assert_equal(reps[r].key(), keys[r])
        var size = 0
        for i in range(len(four)):
            if g_canonical(four[i]) == reps[r]:
                size += 1
        assert_equal(size, sizes[r])


def test_controls() raises:
    # positive control of the degree classifier: (phi^k(0), phi^k(1)) has first
    # defect degree k + 1 (Ochsenschlager; LLR Lemma 30); at k = 4 the kernel
    # says 5+ and the degree-five coordinate 01010 is nonzero
    var expected: List[Int] = [DEGREE_TWO, DEGREE_THREE, DEGREE_FOUR, DEGREE_FIVE_PLUS]
    for k in range(1, 5):
        var p = Pair(thue_morse_block(k, 0), thue_morse_block(k, 1))
        assert_equal(first_defect_degree(p), expected[k - 1])
        # negative control of the irreducibility filter: reducible for k >= 2
        assert_equal(is_irreducible_pair(p), k == 1)
    var t4 = Pair(thue_morse_block(4, 0), thue_morse_block(4, 1))
    var x: List[Int] = [0, 1, 0, 1, 0]
    assert_equal(scattered_count(t4.u, x) - scattered_count(t4.v, x), 64)
    # S(2), S(3) witnesses and a commutation pair (xy, yx), x = 012 ~1 y = 120
    var s2 = Pair(digits("0110"), digits("1001"))
    var s3 = Pair(digits("0110001"), digits("1000110"))
    var xy = Pair(digits("012120"), digits("120012"))
    assert_equal(first_defect_degree(s2), DEGREE_THREE)
    assert_equal(first_defect_degree(s3), DEGREE_FOUR)
    assert_equal(first_defect_degree(xy), DEGREE_THREE)
    var b2: List[Int] = [0, 2, 4]
    var b3: List[Int] = [0, 2, 5, 7]
    var bxy: List[Int] = [0, 3, 6]
    assert_true(coincidence_boundaries(s2.u, s2.v) == b2)
    assert_true(coincidence_boundaries(s3.u, s3.v) == b3)
    assert_true(coincidence_boundaries(xy.u, xy.v) == bxy)
    assert_false(is_irreducible_pair(s2))
    assert_false(is_irreducible_pair(s3))
    assert_false(is_irreducible_pair(xy))


def test_fail_closed() raises:
    var refusals = 0
    try:
        _ = census_length(4, 3)
    except:
        refusals += 1
    try:
        _ = census_length(3, 0)
    except:
        refusals += 1
    try:
        _ = binary_closed_form_ordered(1)
    except:
        refusals += 1
    try:
        var bad: List[Int] = [1, -1, 2]
        _ = class_words(bad)
    except:
        refusals += 1
    try:
        _ = digits("0130")
    except:
        refusals += 1
    # an extension row counts degree-3 pairs without keeping them, and refuses to list them
    var ext = census_length(3, 7, DEGREE_FOUR)
    assert_equal(ext.count(DEGREE_THREE), 6)
    assert_equal(len(ext.pairs), 0)
    try:
        _ = ext.pairs_of_degree(DEGREE_THREE)
    except:
        refusals += 1
    assert_equal(refusals, 6)


def main() raises:
    test_recurrence_against_brute_force()
    test_closed_form_and_catalan()
    test_word_enumeration()
    test_prefix_codes_against_library()
    test_sorted_row_order()
    test_scattered_count_matches_kernels()
    var binary = census_window(2, 20)
    var ternary = census_window(3, 12)
    test_full_table(binary, ternary)
    test_items(ternary)
    test_extension_n13()
    test_controls()
    test_fail_closed()
    print("binomial pair census: full table pinned (d = 2, n <= 20; d = 3, n <= 12); binary calibration against 2 C(n-1) and Table I D_3, D_4; d = 3 minima 7 (K2 = 0) and 12 (~3); n = 7 list = the six seeds; n = 12: twelve ~3 pairs, one G-orbit of w4Pair, none ~4; n = 13: 24 ~3 pairs in three orbits, none ~4.")
    require_contract("Exact census of unordered irreducible distinct balanced word pairs {u, v}, |u| = |v| = n, by first scattered-subword defect degree 2, 3, 4, 5+ (psc/binomial_pairs.mojo): the full table for d = 2, n <= 20 and d = 3, n <= 12 (words, (N1,N2)/(N1..N3)/(N1..N4) class counts, irreducible totals by the lattice-walk recurrence, degree counts, S_3 x reversal x swap classes); binary totals = 2 C(n-1) and binary class counts = Table I D_3(n), D_4(n) of Chrisnata et al.; ternary minimal lengths 7 (K2 = 0) and 12 (K1 = K2 = K3 = 0), the n = 7 list equal to the six psc.seeds pairs, the twelve n = 12 pairs one orbit containing w4Pair = DEGREE4_STATE with K4 != 0 and no irreducible ~4 pair for n <= 12; the n = 13 row (24 ~3 pairs, all K4 != 0, three orbits of sizes 12, 6, 6); the recurrence against brute force (d = 3, n <= 7; d = 2, n <= 12), the prefix-code test against coincidence_boundaries, the Thue-Morse and reducible controls, and the fail-closed refusals")
