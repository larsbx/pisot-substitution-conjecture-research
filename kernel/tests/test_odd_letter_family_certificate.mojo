"""Exact regressions for Theorem K's open family (odd_letter_family_certificate)
and for the opaque segments and many-letter runs of psc.cone_witness.

docs/p1a-a1-prime-2026-10-05.md §3f. The family is sigma(o) = y,
sigma(y) = o w_1 o, sigma(z) = o w_2 o. Lemma Φ1 (w_1 begins with y) and Lemma
Φ2 (w_1 begins with z and the Parikh walks of w_1 and w_2 + e_y cross) name
explicit witness paths; what they leave is the non-crossing pairs, which the
census decides exactly. The pattern tree is an exploratory partial cover: its
certified leaves are proofs on whole regions, its open leaves are reported,
and these tests check that no closed leaf mislabels a member.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.claim_tests import require_contract
from psc.coincidence_formula import coincidence_level
from psc.cone_witness import search_witness, verify_witness, witness_position
from psc.pisot import is_pip
from a1_normal_form_census import shared_tile_between
from odd_letter_family_certificate import (
    A_RUN,
    A_TAIL,
    A_Z,
    LEAF_CERTIFIED,
    LEAF_CUT,
    LEAF_EMPTY,
    LEAF_FAILED,
    LEAF_NOT_MEMBER,
    O,
    Pattern,
    Y,
    Z,
    any_word,
    cover_family,
    crossing,
    family_census,
    family_of,
    identity_subst,
    leaf_index,
    member_sigma,
    _words,
)


def _count(w: List[Int], letter: Int) -> Int:
    var n = 0
    for k in range(len(w)):
        if w[k] == letter:
            n += 1
    return n


def test_det_is_twice_the_z_difference() raises:
    """The determinant is 2 (Z_1 - Z_2) for every pair of words, so membership forces
    |Z_1 - Z_2| = 1."""
    var words = _words(4)
    for a in range(len(words)):
        for b in range(len(words)):
            var m = Mat3(substitution_incidence(member_sigma(words[a], words[b])))
            assert_equal(m.det(), 2 * (_count(words[a], Z) - _count(words[b], Z)))


def test_crossing_is_the_walk_meeting() raises:
    """`crossing` finds (i, k), i, k >= 1, with pi(w1[:i]) = pi(w2[:k]) + e_y
    exactly when one exists, compared with a brute force over all (i, k)."""
    var words = _words(5)
    for a in range(len(words)):
        for b in range(len(words)):
            ref w1 = words[a]
            ref w2 = words[b]
            var brute = False
            for i in range(1, len(w1) + 1):
                for k in range(1, len(w2) + 1):
                    var dy = 0
                    var dz = 0
                    for j in range(i):
                        dy += 1 if w1[j] == Y else 0
                        dz += 1 if w1[j] == Z else 0
                    for j in range(k):
                        dy -= 1 if w2[j] == Y else 0
                        dz -= 1 if w2[j] == Z else 0
                    if dy == 1 and dz == 0:
                        brute = True
            assert_equal(crossing(w1, w2)[0] >= 0, brute)


def test_the_census_reduces_the_family_to_non_crossing_pairs() raises:
    """|w_1|, |w_2| <= 5: every Lemma Φ1 and Φ2 path verifies and names a
    shared tile of the actual words; the non-crossing members are decided
    coincident, at levels 3 to 6."""
    var c = family_census(5)
    assert_equal(c.members, 532)
    assert_equal(c.lemma_failed, 0)
    assert_equal(c.by_phi1, 274)
    assert_equal(c.by_phi2, 138)
    assert_equal(c.non_crossing, 120)
    assert_equal(c.max_level, 6)
    var total = 0
    for k in range(16):
        total += c.levels[k]
    assert_equal(total, 120)
    assert_equal(c.levels[0] + c.levels[1] + c.levels[2], 0)


def test_an_opaque_cone_proves_lemma_phi1() raises:
    """With w_1 = y^(1+n) z T_1 and w_2 = T_2, T_i opaque words, the search
    finds a level-3 path on the whole region -- every primitive w_1 beginning
    with y -- and it names real shared tiles at sample points."""
    var p1 = Pattern(List[Int]([A_RUN, A_Z, A_TAIL]), List[Int]([1, 0, 0]))
    var p2 = any_word()
    var fam = family_of(p1, p2, identity_subst(5))
    var w = search_witness(fam, O, Y, 3, 6, True)
    assert_true(w.found)
    assert_equal(len(w.steps), 3)
    assert_true(verify_witness(fam, O, Y, w.steps))
    for k in range(6):
        var ns = List[Int](length=5, fill=0)
        if k < 5:
            ns[k] = 2
        var sigma = fam.instantiate(ns)
        var pos = witness_position(fam, O, Y, w.steps, ns)
        assert_true(shared_tile_between(sigma, O, Y, len(w.steps), pos))


def test_the_pattern_tree_is_a_sound_partial_cover() raises:
    """Depth 6: the counts are pinned, open leaves are reported rather than
    covered, and against every PIP member with |w_i| <= 5 no empty, cut or
    non-member leaf holds a member, and a certified leaf's level bounds the
    member's exact level."""
    var cov = cover_family(6, 4)
    assert_equal(cov.certified, 14)
    assert_equal(cov.empty, 8)
    assert_equal(cov.cut, 19)
    assert_equal(cov.not_member, 1)
    assert_equal(cov.failed, 34)
    var words = _words(5)
    var in_certified = 0
    var in_open = 0
    for a in range(len(words)):
        for b in range(len(words)):
            var sigma = member_sigma(words[a], words[b])
            var m = Mat3(substitution_incidence(sigma))
            if abs(m.det()) != 2 or not is_pip(m):
                continue
            var li = leaf_index(cov, words[a], words[b], 6)
            assert_true(li >= 0)
            var kind = cov.leaves[li].kind
            assert_false(kind == LEAF_EMPTY or kind == LEAF_CUT or kind == LEAF_NOT_MEMBER)
            if kind == LEAF_CERTIFIED:
                assert_true(coincidence_level(sigma, O, Y) <= cov.leaves[li].level)
                in_certified += 1
            elif kind == LEAF_FAILED:
                in_open += 1
    assert_equal(in_certified, 413)
    assert_equal(in_open, 119)


def main() raises:
    test_det_is_twice_the_z_difference()
    print("[PASS] test_det_is_twice_the_z_difference")
    test_crossing_is_the_walk_meeting()
    print("[PASS] test_crossing_is_the_walk_meeting")
    test_the_census_reduces_the_family_to_non_crossing_pairs()
    print("[PASS] test_the_census_reduces_the_family_to_non_crossing_pairs")
    test_an_opaque_cone_proves_lemma_phi1()
    print("[PASS] test_an_opaque_cone_proves_lemma_phi1")
    test_the_pattern_tree_is_a_sound_partial_cover()
    print("[PASS] test_the_pattern_tree_is_a_sound_partial_cover")
    require_contract("Theorem K's open family sigma(o) = y, sigma(y) = o w_1 o, sigma(z) = o w_2 o: det M = 2 (Z_1 - Z_2); the crossing test agrees with brute force; at |w_i| <= 5 there are 532 PIP members, Lemma Phi1 (w_1 begins with y) names verified level-2/3 paths on 274 and Lemma Phi2 (the Parikh walks of w_1 and w_2 + e_y cross) on 138, none failing, and the 120 non-crossing members are decided coincident at levels 3 to 6; an opaque-tail cone w_1 = y^(1+n) z T_1, w_2 = T_2 carries a level-3 path naming real shared tiles; the exploratory pattern tree at depth 6 has 14 certified, 8 empty, 19 Lemma P1 cut, 1 non-member and 34 open leaves, no closed leaf holds a PIP member it should not, and of the 532 members 413 lie in certified leaves (each at most the leaf level) and 119 in open ones")
