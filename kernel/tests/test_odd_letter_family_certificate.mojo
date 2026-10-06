"""Exact regressions for Theorem K's open family (odd_letter_family_certificate)
and for the opaque segments and many-letter runs of psc.cone_witness.

docs/p1a-a1-prime-2026-10-05.md §3f. The family is sigma(o) = y,
sigma(y) = o w_1 o, sigma(z) = o w_2 o. Lemma Φ1 (w_1 begins with y) and Lemma
Φ2 (w_1 begins with z and the Parikh walks of w_1 and w_2 + e_y cross) name
explicit witness paths; what they leave is the non-crossing pairs, which the
census decides exactly. The delta split (§3g) and the run-shape cover (§3h)
close whole infinite subfamilies. The pattern tree is an exploratory partial cover: its
certified leaves are proofs on whole regions, its open leaves are reported,
and these tests check that no closed leaf mislabels a member.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.claim_tests import require_contract
from psc.coincidence_formula import coincidence_level
from psc.cone_witness import search_witness, search_witness_line, verify_witness, verify_witness_line, witness_position
from std.collections import Dict
from psc.pisot import is_pip
from a1_normal_form_census import f_at, shared_tile_between
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
    NO_DELTA,
    cover_shape,
    crossing,
    delta_census,
    shape_family,
    solve_constraint,
    family_census,
    phi_census,
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


def test_lemmas_phi4_and_phi5_hold_on_every_member() raises:
    """Lemma Φ4: Z_1 = Z_2 + 1 forces Y_1 >= Y_2, and Z_1 = Z_2 - 1 forces
    Y_1 <= Y_2 and Z_2 >= 2 (f(-1) = (1 + Z_2)(Y_2 - Y_1 - 1) and
    f(1) = (Z_2 - 1)(Y_1 - Y_2 - 1) respectively). Lemma Φ5: with
    Z_1 = Z_2 + 1, a non-crossing w_1 is u y^(Y_1 - Y_2) with
    pi(u) = pi(w_2) + e_z. Checked on all 2,136 members with |w_i| <= 6."""
    var d = delta_census(6, False)
    assert_equal(d.members, 2136)
    assert_equal(d.sign_violations, 0)
    assert_equal(d.non_crossing, 388)
    assert_equal(d.shape_violations, 0)


def test_lemmas_phi6_to_phi8_close_the_delta_ez_cell() raises:
    """At |w_i| <= 7 every Lemma Φ6, Φ7 or Φ8 path verifies and names a shared
    tile of the words (1,180 of the 1,267 non-crossing members); in the cell
    delta = e_z the only member left is (zz, z), decided at level 6, and the
    word pair (z, empty) is not PIP. The residue of the other cells is
    decided exactly, at levels 3 to 6."""
    var p = phi_census(7)
    assert_equal(p.non_crossing, 1267)
    assert_equal(p.by_lemma, 1180)
    assert_equal(p.lemma_failed, 0)
    assert_equal(p.cell_ez_residue, 1)
    assert_equal(p.residue_levels[3], 38)
    assert_equal(p.residue_levels[4], 42)
    assert_equal(p.residue_levels[5], 6)
    assert_equal(p.residue_levels[6], 1)
    assert_equal(coincidence_level(member_sigma(List[Int]([Z, Z]), List[Int]([Z])), O, Y), 6)
    assert_false(is_pip(Mat3(substitution_incidence(member_sigma(List[Int]([Z]), List[Int]())))))


def _key(v: List[Int]) -> String:
    var out = String("")
    for k in range(len(v)):
        out += String(v[k]) + ","
    return out


def test_the_constraint_substitutions_partition_the_solutions() raises:
    """The equation sum_pos n - sum_neg n = target over n >= 0: the regions solve_constraint
    returns hit every solution in a box exactly once, for several targets."""
    var pos = List[Int]([0, 2])
    var neg = List[Int]([1, 3])
    var box = 5
    for target in range(-3, 4):
        var regions = solve_constraint(identity_subst(4), pos, neg, target)
        var hits = Dict[String, Int]()
        for r in range(len(regions)):
            ref f = regions[r]
            for idx in range(1296):  # 6^4 points of the free variables
                var ns = List[Int]()
                var rest = idx
                var dead_moved = False
                for j in range(4):
                    ns.append(rest % 6)
                    rest //= 6
                    var live = False
                    for k in range(4):
                        if f[k][j + 1] != 0:
                            live = True
                    if not live and ns[j] != 0:
                        dead_moved = True
                if dead_moved:
                    continue  # a variable the region fixed: one representative
                var img = List[Int]()
                var inside = True
                for k in range(4):
                    var v = f[k][0]
                    for j in range(4):
                        v += f[k][j + 1] * ns[j]
                    if v < 0 or v > box:
                        inside = False
                    img.append(v)
                if not inside:
                    continue
                assert_equal(img[0] + img[2] - img[1] - img[3], target)
                var key = _key(img)
                if key in hits:
                    hits[key] = hits[key] + 1
                else:
                    hits[key] = 1
        var solutions = 0
        for idx in range(1296):
            var v = List[Int]()
            var rest = idx
            for _ in range(4):
                v.append(rest % 6)
                rest //= 6
            if v[0] + v[2] - v[1] - v[3] != target:
                continue
            solutions += 1
            var key = _key(v)
            assert_true(key in hits)
        assert_equal(len(hits), solutions)
        for e in hits.items():
            assert_equal(e.value, 1)


def test_the_quadratic_pisot_identities() raises:
    """The identities f(1) = Z_2 (Delta - 1) - 2 Y_2 - Delta - 3 when Z_1 = Z_2 + 1, and
    f(-1) = Z_2 (|Delta| - 1) - 2 Y_1 - |Delta| + 3 when Z_1 = Z_2 - 1, exactly,
    for the substitution with w_1 = y^Y_1 z^Z_1 and w_2 = y^Y_2 z^Z_2."""
    for y2 in range(5):
        for z2 in range(1, 5):
            for d in range(5):
                var w1 = List[Int]()
                var w2 = List[Int]()
                for _ in range(y2 + d):
                    w1.append(Y)
                for _ in range(z2 + 1):
                    w1.append(Z)
                for _ in range(y2):
                    w2.append(Y)
                for _ in range(z2):
                    w2.append(Z)
                var m = Mat3(substitution_incidence(member_sigma(w1, w2)))
                assert_equal(f_at(m, 1), z2 * (d - 1) - 2 * y2 - d - 3)
                var v1 = List[Int]()
                var v2 = List[Int]()
                for _ in range(y2):
                    v1.append(Y)
                for _ in range(z2 - 1):
                    v1.append(Z)
                for _ in range(y2 + d):
                    v2.append(Y)
                for _ in range(z2):
                    v2.append(Z)
                var m2 = Mat3(substitution_incidence(member_sigma(v1, v2)))
                if z2 >= 2:
                    assert_equal(f_at(m2, -1), z2 * (d - 1) - 2 * y2 - d + 3)


def test_line_mode_reaches_offsets_affine_along_the_delta_line() raises:
    """On (z^a y^b, y^(b+1) z^(a+1)) with a = b + 2 + n1, b = 2 + n2 the line
    search finds a path and it verifies on the whole region. That line mode
    is needed somewhere is pinned by test_shape_cells_that_close, whose
    Delta = -1 cell uses it."""
    var subst = List[List[Int]]()
    subst.append(List[Int]([3, 1, 1]))  # a - 1 = b + 1 + n1 = 3 + n1 + n2
    subst.append(List[Int]([1, 0, 1]))  # b - 1 = 1 + n2
    subst.append(List[Int]([2, 0, 1]))  # b + 1 - 1
    subst.append(List[Int]([4, 1, 1]))  # a + 1 - 1
    var fam = shape_family(List[Int]([Z, Y]), List[Int]([Y, Z]), subst)
    var w = search_witness_line(fam, O, Y, 3, 6, Y, Z)
    assert_true(w.found)
    assert_true(verify_witness_line(fam, O, Y, w.steps))


def test_shape_cells_that_close() raises:
    """Whole infinite shape families, every Delta: (zy | ε), (zy | z) and
    (zy | yz) with Z_1 = Z_2 + 1 close with no open region; (zy | yz) with
    Z_1 = Z_2 - 1 closes at Delta = -1 (line mode needed)."""
    var zy = List[Int]([Z, Y])
    var c0 = cover_shape(zy, List[Int](), 1, NO_DELTA, 4)
    assert_equal(c0.open, 0)
    assert_equal(c0.certified, 1)
    for d in range(1, 5):
        var c1 = cover_shape(zy, List[Int]([Z]), 1, d, 4, d == 4)
        assert_equal(c1.open, 0)
        var c2 = cover_shape(zy, List[Int]([Y, Z]), 1, d, 4, d == 4)
        assert_equal(c2.open, 0)
    var c3 = cover_shape(zy, List[Int]([Y, Z]), -1, -1, 4)
    assert_equal(c3.open, 0)
    assert_true(c3.line_certified >= 1)


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
    test_lemmas_phi4_and_phi5_hold_on_every_member()
    print("[PASS] test_lemmas_phi4_and_phi5_hold_on_every_member")
    test_lemmas_phi6_to_phi8_close_the_delta_ez_cell()
    print("[PASS] test_lemmas_phi6_to_phi8_close_the_delta_ez_cell")
    test_the_constraint_substitutions_partition_the_solutions()
    print("[PASS] test_the_constraint_substitutions_partition_the_solutions")
    test_the_quadratic_pisot_identities()
    print("[PASS] test_the_quadratic_pisot_identities")
    test_line_mode_reaches_offsets_affine_along_the_delta_line()
    print("[PASS] test_line_mode_reaches_offsets_affine_along_the_delta_line")
    test_shape_cells_that_close()
    print("[PASS] test_shape_cells_that_close")
    require_contract("Theorem K's open family sigma(o) = y, sigma(y) = o w_1 o, sigma(z) = o w_2 o: det M = 2 (Z_1 - Z_2); the crossing test agrees with brute force; at |w_i| <= 5 there are 532 PIP members, Lemma Phi1 (w_1 begins with y) names verified level-2/3 paths on 274 and Lemma Phi2 (the Parikh walks of w_1 and w_2 + e_y cross) on 138, none failing, and the 120 non-crossing members are decided coincident at levels 3 to 6; an opaque-tail cone w_1 = y^(1+n) z T_1, w_2 = T_2 carries a level-3 path naming real shared tiles; the exploratory pattern tree at depth 6 has 14 certified, 8 empty, 19 Lemma P1 cut, 1 non-member and 34 open leaves, no closed leaf holds a PIP member it should not, and of the 532 members 413 lie in certified leaves (each at most the leaf level) and 119 in open ones; Lemma Phi4 (Pisot signs of Y_1 - Y_2 against Z_1 - Z_2) and Lemma Phi5 (the Z_1 = Z_2 + 1 non-crossing shape w_1 = u y^(Y_1 - Y_2), pi(u) = pi(w_2) + e_z) hold on all 2,136 members with |w_i| <= 6; at |w_i| <= 7 the Lemma Phi6-Phi8 paths verify on 1,180 of the 1,267 non-crossing members with none failing, the delta = e_z cell leaves only (zz, z) at level 6, (z, empty) is not PIP, and the other cells leave 87 members decided at levels 3 to 6; the run-shape cover: solve_constraint partitions the solutions of sum_pos n - sum_neg n = target exactly (every box solution hit once, targets -3..3), the quadratic Lemma P1 identities f(1) = Z_2 (Delta - 1) - 2 Y_2 - Delta - 3 (Z_1 = Z_2 + 1) and f(-1) = Z_2 (|Delta| - 1) - 2 Y_1 - |Delta| + 3 (Z_1 = Z_2 - 1) hold, a line-mode path (offsets affine along e_z - e_y) verifies on (z^a y^b, y^(b+1) z^(a+1)), a >= b + 2, and the shape cells (zy | eps), (zy | z), (zy | yz) with Z_1 = Z_2 + 1 close for Delta = 1, 2, 3 and the tail Delta >= 4 with no open region, while (zy | yz) with Z_1 = Z_2 - 1 closes at Delta = -1 using line mode")
