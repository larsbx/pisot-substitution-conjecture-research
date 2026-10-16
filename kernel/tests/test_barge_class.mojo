"""Regressions for Barge-class conjugacy witnesses (`psc.barge_class`)."""

from std.testing import assert_equal, assert_false, assert_true
from psc.barge_class import (
    KIND_DIRECT,
    KIND_LEFT_ROTATION,
    barge_witness,
    common_prefix_length,
    common_suffix_length,
    in_barge_class,
    in_mirror_class,
    rotate_left,
    rotate_right,
)
from mojo_smoke.claims import require_contract
from psc.dumont_thomas import power_substitution


def _ternary_good_exit(k: Int, h: Int) -> List[List[Int]]:
    # a -> a^k b c^h, b -> ab, c -> a. Endpoint predicates are
    # word-combinatorial, so this intentionally does NOT run the screened
    # cubic PIP classifier at the longer k=6, h=5 parameter.
    var a = List[Int]()
    for _ in range(k):
        a.append(0)
    a.append(1)
    for _ in range(h):
        a.append(2)
    var b: List[Int] = [0, 1]
    var c: List[Int] = [0]
    var sigma = List[List[Int]]()
    sigma.append(a^)
    sigma.append(b^)
    sigma.append(c^)
    return sigma^


def test_ternary_good_exit_family_is_direct_mirror_barge() raises:
    # k=3,h=2 is the overlap regression; k=6,h=5 is an out-of-screen
    # family member. Both have constant first letter a and pairwise
    # distinct last letters c,b,a, so reversal satisfies Barge Thm 3.13.
    for t in range(2):
        var k = 3
        var h = 2
        if t == 1:
            k = 6
            h = 5
        var sigma = _ternary_good_exit(k, h)
        assert_true(in_mirror_class(sigma))
        assert_false(in_barge_class(sigma))
        var w = barge_witness(sigma, 1)
        assert_true(w.found())
        assert_equal(w.power, 1)
        assert_equal(w.kind, KIND_DIRECT)
        assert_true(w.mirror)


def test_tribonacci_is_in_the_mirror_class() raises:
    """`0 -> 01, 1 -> 02, 2 -> 0`: constant on initial letters, injective on
    final letters (a classical pure-discrete-spectrum case)."""
    var w = barge_witness([[0, 1], [0, 2], [0]], 6)
    assert_equal(w.power, 1)
    assert_equal(w.kind, KIND_DIRECT)
    assert_true(w.mirror)


def test_catch_up_free_specimen_has_a_square_in_barges_class() raises:
    """`0 -> 1, 1 -> 22, 2 -> 012` (catch-up-free, the first total Q1 failure):
    `sigma^2 = (22, 012012, 122012)` is injective on initial letters and
    constant on final letters."""
    var sigma: List[List[Int]] = [[1], [2, 2], [0, 1, 2]]
    var square = power_substitution(sigma, 2)
    assert_true(in_barge_class(square))
    var w = barge_witness(sigma, 6)
    assert_equal(w.power, 2)
    assert_equal(w.kind, KIND_DIRECT)
    assert_false(w.mirror)


def test_left_rotation_by_the_common_prefix() raises:
    """`0 -> 00, 1 -> 010, 2 -> 020` is constant on both ends; rotating by the
    common prefix `0` gives `(00, 100, 200)`, which is in Barge's class."""
    var t: List[List[Int]] = [[0, 0], [0, 1, 0], [0, 2, 0]]
    assert_false(in_barge_class(t) or in_mirror_class(t))
    assert_equal(common_prefix_length(t), 1)
    var r = rotate_left(t, 1)
    assert_true(in_barge_class(r))
    assert_equal(r[1][0], 1)
    var back = rotate_right(r, 1)
    for a in range(3):
        assert_equal(len(back[a]), len(t[a]))
        for i in range(len(t[a])):
            assert_equal(back[a][i], t[a][i])
    var w = barge_witness(t, 1)
    assert_equal(w.kind, KIND_LEFT_ROTATION)


def _class_d(p: Int, q: Int, r: Int) -> List[List[Int]]:
    # x -> x y^p c, c -> c y^q x, y -> c y^r c.
    # The endpoint theorem holds even without a Pisot certificate; this is
    # word-only testing, not a call to the screened cubic PIP classifier.
    var x: List[Int] = [0]
    for _ in range(p):
        x.append(2)
    x.append(1)
    var c: List[Int] = [1]
    for _ in range(q):
        c.append(2)
    c.append(0)
    var y: List[Int] = [1]
    for _ in range(r):
        y.append(2)
    y.append(1)
    var sigma = List[List[Int]]()
    sigma.append(x^)
    sigma.append(c^)
    sigma.append(y^)
    return sigma^


def test_class_d_has_no_barge_power_or_common_rotation() raises:
    # Representative exact boundary/interior controls. The all-powers result
    # is the endpoint-map proof, not a conclusion from bounded testing.
    var cases: List[List[Int]] = [[3, 2, 0], [5, 6, 4], [4, 3, 3]]
    for j in range(len(cases)):
        var sigma = _class_d(cases[j][0], cases[j][1], cases[j][2])
        for n in range(1, 4):
            var t = power_substitution(sigma, n)
            # f^n=(x,c,c), g^odd=(c,x,c), g^even=(x,c,x).
            assert_equal(t[0][0], 0)
            assert_equal(t[1][0], 1)
            assert_equal(t[2][0], 1)
            if n % 2 == 1:
                assert_equal(t[0][len(t[0]) - 1], 1)
                assert_equal(t[1][len(t[1]) - 1], 0)
                assert_equal(t[2][len(t[2]) - 1], 1)
            else:
                assert_equal(t[0][len(t[0]) - 1], 0)
                assert_equal(t[1][len(t[1]) - 1], 1)
                assert_equal(t[2][len(t[2]) - 1], 0)
            assert_equal(common_prefix_length(t), 0)
            assert_equal(common_suffix_length(t), 0)
            assert_false(in_barge_class(t))
            assert_false(in_mirror_class(t))
        assert_false(barge_witness(sigma, 3).found())


def test_plastic_has_no_witness() raises:
    var w = barge_witness([[1], [2], [0, 1]], 6)
    assert_false(w.found())


def main() raises:
    test_ternary_good_exit_family_is_direct_mirror_barge()
    test_tribonacci_is_in_the_mirror_class()
    test_catch_up_free_specimen_has_a_square_in_barges_class()
    test_left_rotation_by_the_common_prefix()
    test_class_d_has_no_barge_power_or_common_rotation()
    test_plastic_has_no_witness()
    print("[PASS] Barge-class witnesses: mirror control, catch-up-free square, rotation, no-witness control")
    require_contract("class-D x->xy^p c, c->cy^q x, y->cy^r c has no Barge or mirror witness at powers 1..3, no nonempty common prefix or suffix, for two residual boundary parameter pairs and one upper family point")
    require_contract("a -> a^k b c^h, b -> ab, c -> a is directly in mirror Barge class for (k,h)=(3,2) and (6,5), with no need for powers or rotation; no long-image PIP screening")
    require_contract("Barge-class membership of a power or maximal common-prefix/suffix rotation is decided exactly; Tribonacci is in the mirror class, 0 -> 1, 1 -> 22, 2 -> 012 has its square in Barge's class, the plastic substitution has no witness up to power 6")
