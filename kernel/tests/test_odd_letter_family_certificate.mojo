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
from psc.cone_witness import aff_eval, monotone_paths_meet, Prover, _q_eval, _q_lin, _q_nonneg_under, _qa, search_crossing, search_witness, search_witness_line, verify_crossing, verify_witness, verify_witness_line, witness_position
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
    RunPattern,
    cover_shape,
    pattern_matches,
    refine_pattern,
    cover_pattern,
    common_points,
    residue_members,
    RUN_TREE_SPLITS,
    RUN_TREE_PEEL,
    RUN_TREE_BUDGET,
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
    concrete_family,
    reveal_census,
    impose_nonneg,
    impose_equal,
    cover_pattern_guided,
    tighten,
    propagate_bounds,
    search_point,
    zcap_cover,
    mccormick_cut,
    pisot_carve_forms,
    _aff_times,
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


def test_pattern_refinement_partitions_the_word_pairs() raises:
    """Refining the root z* | * three times over: every word pair with w_1
    beginning with z, both words of length <= 5, lies in exactly one leaf."""
    var leaves = List[RunPattern]()
    var frontier = List[RunPattern]()
    frontier.append(RunPattern(List[Int]([Z]), True, List[Int](), True))
    for _ in range(4):
        var nxt = List[RunPattern]()
        for k in range(len(frontier)):
            var kids = refine_pattern(frontier[k])
            if len(kids) == 0:
                leaves.append(frontier[k].copy())
            for j in range(len(kids)):
                nxt.append(kids[j].copy())
        frontier = nxt^
    for k in range(len(frontier)):
        leaves.append(frontier[k].copy())
    var words = _words(5)
    var pairs = 0
    for a in range(len(words)):
        if len(words[a]) == 0 or words[a][0] != Z:
            continue
        for b in range(len(words)):
            var hits = 0
            for k in range(len(leaves)):
                if pattern_matches(leaves[k], words[a], words[b]):
                    hits += 1
            assert_equal(hits, 1)
            pairs += 1
    assert_equal(pairs, 31 * 63)


def test_run_patterns_with_a_tail_close() raises:
    """Induction on runs, cell Z_1 = Z_2 + 1, Delta = 1 (Theorem Xi): the nine
    closed leaves of the cell's run tree close with no open region; those with
    an opaque tail are infinite families with unboundedly many runs."""
    var zy = List[Int]([Z, Y])
    var cases = List[RunPattern]()
    cases.append(RunPattern(zy.copy(), False, zy.copy(), True))
    cases.append(RunPattern(zy.copy(), False, List[Int]([Y, Z]), True))
    cases.append(RunPattern(zy.copy(), True, List[Int]([Z]), False))
    cases.append(RunPattern(zy.copy(), True, List[Int]([Y]), False))
    cases.append(RunPattern(List[Int]([Z, Y, Z]), True, zy.copy(), False))
    cases.append(RunPattern(List[Int]([Z, Y, Z]), True, List[Int]([Y, Z]), False))
    for k in range(len(cases)):
        var c = cover_pattern(cases[k], 1, 1, RUN_TREE_SPLITS, False, RUN_TREE_PEEL, RUN_TREE_BUDGET)
        assert_equal(c.open, 0)
        assert_true(c.certified >= 1)
    # The rest of the cell's closed leaves: no member, or one point decided.
    var rest = List[RunPattern]()
    rest.append(RunPattern(List[Int]([Z]), False, List[Int]([Z]), True))
    rest.append(RunPattern(List[Int]([Z]), False, List[Int]([Y]), True))
    rest.append(RunPattern(List[Int]([Z]), True, List[Int](), False))
    for k in range(len(rest)):
        assert_equal(cover_pattern(rest[k], 1, 1, RUN_TREE_SPLITS, False, RUN_TREE_PEEL, RUN_TREE_BUDGET).open, 0)
    # Negative control: the doubly open pattern is not closed at this budget.
    var both = cover_pattern(RunPattern(zy.copy(), True, zy.copy(), True), 1, 1, RUN_TREE_SPLITS, False, RUN_TREE_PEEL, RUN_TREE_BUDGET)
    assert_true(both.open > 0)


def _parikh_yz(w: List[Int], n: Int) -> List[Int]:
    var out = List[Int]([0, 0])
    for k in range(n):
        out[0 if w[k] == Y else 1] += 1
    return out^


def test_the_residue_is_mostly_one_excursion() raises:
    """Common points agree with their definition, and of the 87 residual
    members at |w_i| <= 7, 51 have only the start point t = 1: their walks
    separate at once and meet no more."""
    var words = _words(4)
    for a in range(len(words)):
        for b in range(len(words)):
            var n = 0
            for t in range(1, len(words[a])):
                if t > len(words[b]):
                    break
                var p1 = _parikh_yz(words[a], t)
                var p2 = _parikh_yz(words[b], t - 1)
                if p1[0] == p2[0] and p1[1] == p2[1] + 1:
                    n += 1
            assert_equal(common_points(words[a], words[b]), n)
    var residue = residue_members(7)
    assert_equal(len(residue), 87)
    var hist = List[Int](length=8, fill=0)
    for k in range(len(residue)):
        hist[common_points(residue[k].w1, residue[k].w2)] += 1
    assert_equal(hist[0], 6)
    assert_equal(hist[1], 51)
    assert_equal(hist[2], 22)
    assert_equal(hist[3] + hist[4] + hist[5], 8)


def _path(start: List[Int], w: List[Int]) -> List[List[Int]]:
    """The monotone lattice path of `w` from `start`, coordinates (y, z)."""
    var out = List[List[Int]]()
    out.append(start.copy())
    for k in range(len(w)):
        var p = out[k].copy()
        p[0 if w[k] == Y else 1] += 1
        out.append(p^)
    return out^


def _first_meeting(pp: List[List[Int]], qq: List[List[Int]]) -> Int:
    """Least level at which the two paths share a point, or -1."""
    var best = -1
    for i in range(len(pp)):
        for k in range(len(qq)):
            if pp[i][0] == qq[k][0] and pp[i][1] == qq[k][1]:
                var n = pp[i][0] + pp[i][1]
                if best < 0 or n < best:
                    best = n
    return best


def test_lemma_x_on_every_small_pair_of_monotone_paths() raises:
    """Lemma X by brute force against psc.cone_witness.monotone_paths_meet: for every
    pair of monotone paths of at most 4 steps, Q starting in a box around P's
    start, Q starting weakly on one side of P and ending strictly on the other
    forces a shared point before the last common level; with a weak end, at or
    before it. A weak end alone can leave the only shared point at the last
    common level -- the negative control for strictness at a word's end."""
    var words = _words(4)
    var strict_cases = 0
    var weak_only_at_end = 0
    for a in range(len(words)):
        var pp = _path(List[Int]([0, 0]), words[a])
        ref p0 = pp[0]
        ref p1 = pp[len(pp) - 1]
        for b in range(len(words)):
            for qy in range(-2, 3):
                for qz in range(-2, 3):
                    var qq = _path(List[Int]([qy, qz]), words[b])
                    ref q0 = qq[0]
                    ref q1 = qq[len(qq) - 1]
                    var nlo = max(p0[0] + p0[1], q0[0] + q0[1])
                    var nhi = min(p1[0] + p1[1], q1[0] + q1[1])
                    if nlo > nhi:
                        continue
                    var strict = monotone_paths_meet(p0, p1, q0, q1, False)
                    var weak = monotone_paths_meet(p0, p1, q0, q1, True)
                    var meet = _first_meeting(pp, qq)
                    if strict:
                        strict_cases += 1
                        assert_true(meet >= nlo and meet < nhi)
                    if weak:
                        assert_true(meet >= nlo and meet <= nhi)
                        if meet == nhi and not strict:
                            weak_only_at_end += 1
    assert_true(strict_cases > 1000)
    assert_true(weak_only_at_end > 0)


def test_crossing_closures_are_shared_tiles() raises:
    """Wherever the cone search closes a residual member by Lemma X, the exact
    decider finds the shared tile within two levels of the path's end; on the
    87 residual members at |w_i| <= 7 every one but (zz, z) closes this way."""
    var res = residue_members(7)
    var closed = 0
    for r in range(len(res)):
        ref m = res[r]
        var sigma = member_sigma(m.w1, m.w2)
        var fam = concrete_family(sigma)
        var c = search_crossing(fam, O, Y, 12, 4, Y, Z, Y, Z)
        if not c.found:
            assert_equal(len(m.w1), 2)
            continue
        assert_true(verify_crossing(fam, O, Y, c.steps, c.close[0], Y, Z))
        var lev = coincidence_level(sigma, O, Y)
        assert_true(lev >= 0 and lev <= len(c.steps) + 2)
        closed += 1
    assert_equal(closed, 86)


def test_lemma_phi5_prime_the_short_suffix_of_w2() raises:
    """Lemma Phi5': with Z_2 = Z_1 + 1 and the walks not crossing, Delta <= 0,
    |w_2| = |w_1| + 1 - Delta, and the suffix of w_2 after its first
    |w_1| - 1 letters holds at least two z; on every member with |w_i| <= 7."""
    var words = _words(7)
    var checked = 0
    for a in range(len(words)):
        ref w1 = words[a]
        if len(w1) < 2 or w1[0] != Z:
            continue
        for b in range(len(words)):
            ref w2 = words[b]
            if _count(w2, Z) != _count(w1, Z) + 1 or crossing(w1, w2)[0] >= 0:
                continue
            if not is_pip(Mat3(substitution_incidence(member_sigma(w1, w2)))):
                continue
            var dy = _count(w1, Y) - _count(w2, Y)
            assert_true(dy <= 0)
            assert_equal(len(w2), len(w1) + 1 - dy)
            var zs = 0
            for k in range(len(w1) - 1, len(w2)):
                zs += 1 if w2[k] == Z else 0
            assert_true(zs >= 2)
            checked += 1
    assert_true(checked > 100)


def test_reveal_census_needs_at_most_two_runs_to_length_7() raises:
    """With the suffix of Lemma Phi5 / Phi5', the synchronized and lagged
    cuts, every non-crossing PIP member whose longer word has length 5, 6 or
    7 has a Lemma X certificate reading at most its first two runs."""
    var h5 = reveal_census(5, 6, 8)
    assert_equal(h5[0], 0)
    assert_equal(h5[1], 77)
    assert_equal(h5[2], 4)
    var h6 = reveal_census(6, 6, 8)
    assert_equal(h6[1], 255)
    assert_equal(h6[2], 13)
    var h7 = reveal_census(7, 6, 8)
    assert_equal(h7[0], 0)
    assert_equal(h7[1], 825)
    assert_equal(h7[2], 54)
    for r in range(3, len(h7)):
        assert_equal(h7[r], 0)


def test_cover_pattern_closes_regions_by_lemma_x() raises:
    """On the doubly open pattern zyz* y^Delta | zyz* (Lemma Phi5 suffix,
    Delta = 1) the cone search certifies regions by Lemma X, each verified on
    the whole region (a failed verification raises)."""
    var zyz = List[Int]([Z, Y, Z])
    var c = cover_pattern(RunPattern(zyz.copy(), True, zyz.copy(), True, List[Int]([Y])), 1, 1, RUN_TREE_SPLITS, False, RUN_TREE_PEEL, 100)
    assert_true(c.crossing_certified >= 1)


def _live_vars(forms: List[List[Int]], m: Int) -> List[Int]:
    var out = List[Int]()
    for k in range(m):
        for i in range(len(forms)):
            if forms[i][k + 1] != 0:
                out.append(k)
                break
    return out^


def test_impose_nonneg_partitions_exactly() raises:
    """For every form a_0 + a_1 n_1 + a_2 n_2 with a_0 in -4..4 and a_1, a_2 in
    -3..3, the regions of impose_nonneg hit each point of the box [0, 5]^2 with
    F >= 0 exactly once, never a point with F < 0, and carry F with
    nonnegative coefficients."""
    var B = 5
    for a0 in range(-4, 5):
        for a1 in range(-3, 4):
            for a2 in range(-3, 4):
                var F = List[Int]([a0, a1, a2])
                var forms = identity_subst(2)
                forms.append(F.copy())
                var regs = impose_nonneg(forms, 2)
                var hits = List[Int](length=(B + 1) * (B + 1), fill=0)
                for r in range(len(regs)):
                    ref g = regs[r]
                    for k in range(len(g[2])):
                        assert_true(g[2][k] >= 0)
                    var lv = _live_vars(g, 2)
                    var span = 1
                    for _ in range(len(lv)):
                        span *= 3 * B + 1
                    for code in range(span):
                        var ns = List[Int](length=2, fill=0)
                        var x = code
                        for j in range(len(lv)):
                            ns[lv[j]] = x % (3 * B + 1)
                            x //= 3 * B + 1
                        var p0 = aff_eval(g[0], ns)
                        var p1 = aff_eval(g[1], ns)
                        assert_true(a0 + a1 * p0 + a2 * p1 >= 0)
                        if p0 <= B and p1 <= B:
                            hits[p0 * (B + 1) + p1] += 1
                for p0 in range(B + 1):
                    for p1 in range(B + 1):
                        var want = 1 if a0 + a1 * p0 + a2 * p1 >= 0 else 0
                        assert_equal(hits[p0 * (B + 1) + p1], want)


def test_guided_partition_closes_a_doubly_open_pattern() raises:
    """zy* y | zy* in the cell Z_1 = Z_2 + 1, Delta = 1 (Lemma Phi5 suffix):
    both words keep an opaque tail, the blind cover leaves regions open, and
    the certificate-guided partition closes it -- every carved region checked
    again by the ordinary verifier."""
    var zy = List[Int]([Z, Y])
    var c = cover_pattern_guided(RunPattern(zy.copy(), True, zy.copy(), True, List[Int]([Y])), 1, 1, 2000)
    assert_equal(c.open, 0)
    assert_false(c.budget_exhausted)
    assert_true(c.certified >= 50)


def test_impose_equal_partitions_exactly() raises:
    """For every form E = a_0 + a_1 n_1 + a_2 n_2 with a_0 in -4..4 and
    a_1, a_2 in -2..2, the regions of impose_equal hit each point of the box
    [0, 6]^2 with E = 0 exactly once and no other point."""
    var B = 6
    for a0 in range(-4, 5):
        for a1 in range(-2, 3):
            for a2 in range(-2, 3):
                var forms = identity_subst(2)
                forms.append(List[Int]([a0, a1, a2]))
                var regs = impose_equal(forms, 2)
                var hits = List[Int](length=(B + 1) * (B + 1), fill=0)
                for r in range(len(regs)):
                    ref g = regs[r]
                    var lv = _live_vars(g, 2)
                    var span = 1
                    for _ in range(len(lv)):
                        span *= 3 * B + 1
                    for code in range(span):
                        var ns = List[Int](length=2, fill=0)
                        var x = code
                        for j in range(len(lv)):
                            ns[lv[j]] = x % (3 * B + 1)
                            x //= 3 * B + 1
                        var p0 = aff_eval(g[0], ns)
                        var p1 = aff_eval(g[1], ns)
                        assert_equal(a0 + a1 * p0 + a2 * p1, 0)
                        if p0 <= B and p1 <= B:
                            hits[p0 * (B + 1) + p1] += 1
                for p0 in range(B + 1):
                    for p1 in range(B + 1):
                        var want = 1 if a0 + a1 * p0 + a2 * p1 == 0 else 0
                        assert_equal(hits[p0 * (B + 1) + p1], want)


def _small_forms(c_lo: Int, c_hi: Int, a: Int) -> List[List[Int]]:
    var out = List[List[Int]]()
    for c in range(c_lo, c_hi + 1):
        for a1 in range(-a, a + 1):
            for a2 in range(-a, a + 1):
                out.append(List[Int]([c, a1, a2]))
    return out^


def test_tighten_keeps_the_integer_points() raises:
    """tighten(F) >= 0 exactly where F >= 0 on the box [0, 6]^2, for every
    F = a_0 + a_1 n_1 + a_2 n_2 with a_0 in -6..6 and a_1, a_2 in -3..3."""
    var forms = _small_forms(-6, 6, 3)
    for k in range(len(forms)):
        var t = tighten(forms[k])
        for p0 in range(7):
            for p1 in range(7):
                var ns = List[Int]([p0, p1])
                assert_equal(aff_eval(forms[k], ns) >= 0, aff_eval(t, ns) >= 0)


def test_the_prover_is_sound_on_its_regions() raises:
    """Whenever the prover shows F >= 0 (affine) or Q >= 0 (Q = U V + W)
    under one or two assumptions, F or Q is >= 0 at every point of the box
    [0, 5]^2 where the assumptions hold; with no assumptions it is the
    coefficient-sign test, and it proves an assumption, twice an
    assumption, and an assumption's tightening's source."""
    var assume = _small_forms(-1, 1, 1)
    var targets = _small_forms(-2, 2, 2)
    var proved = 0
    for i in range(len(assume)):
        for j in range(i, len(assume)):
            var pv = Prover(List[List[Int]]([assume[i].copy(), assume[j].copy()]))
            for k in range(len(targets)):
                var q = _q_lin(_aff_times(assume[i], targets[k]), _qa(targets[(7 * k + 3) % len(targets)]), 1)
                var aff_ok = pv.nonneg(targets[k])
                var q_ok = _q_nonneg_under(q, pv)
                if aff_ok:
                    proved += 1
                for p0 in range(6):
                    for p1 in range(6):
                        var ns = List[Int]([p0, p1])
                        if aff_eval(assume[i], ns) < 0 or aff_eval(assume[j], ns) < 0:
                            continue
                        if aff_ok:
                            assert_true(aff_eval(targets[k], ns) >= 0)
                        if q_ok:
                            assert_true(_q_eval(q, ns) >= 0)
    assert_true(proved > 10000)
    assert_true(Prover().nonneg(List[Int]([0, 1, 2])))
    assert_false(Prover().nonneg(List[Int]([1, -1, 2])))
    var a = List[Int]([-3, 2, -4])
    var pv = Prover(List[List[Int]]([tighten(a)]))
    assert_true(pv.nonneg(a))
    assert_true(pv.nonneg(List[Int]([-4, 3, -4])))
    assert_true(Prover(List[List[Int]]([a.copy()])).nonneg(List[Int]([-6, 4, -8])))
    assert_true(Prover(List[List[Int]]([a.copy(), List[Int]([3, -2, 4])])).vanishes(a))


def test_mccormick_quadrants_hold_no_pip_member() raises:
    """For s = +1 and s = -1, a two-parameter family of counts (Y_1, Z_1,
    Y_2, Z_2) and every point p of [0, 6]^2 where Lemma P1's f >= 0: the
    quadrant G_1, G_2, G_3 >= 0 of pisot_carve_forms contains p, mccormick_cut
    accepts it under its tightened forms, and f >= 0 at every box point in it."""
    var carved = 0
    for s in [1, -1]:
        var counts = List[List[Int]]()
        if s == 1:
            # Y_1 = Y_2 + 1 + n_1, Z_1 = Z_2 + 1, Y_2 = n_2, Z_2 = 1 + n_1 + n_2
            counts.append(List[Int]([1, 1, 1]))
            counts.append(List[Int]([2, 1, 1]))
            counts.append(List[Int]([0, 0, 1]))
            counts.append(List[Int]([1, 1, 1]))
        else:
            # Y_1 = n_2, Z_1 = Z_2 - 1, Y_2 = Y_1 + 1 + n_1, Z_2 = 2 + n_1 + n_2
            counts.append(List[Int]([0, 0, 1]))
            counts.append(List[Int]([1, 1, 1]))
            counts.append(List[Int]([1, 1, 1]))
            counts.append(List[Int]([2, 1, 1]))
        for p0 in range(7):
            for p1 in range(7):
                var ns = List[Int]([p0, p1])
                var g = pisot_carve_forms(counts, s, ns)
                if len(g) == 0:
                    continue
                carved += 1
                var tight = List[List[Int]]()
                for k in range(3):
                    assert_true(aff_eval(g[k], ns) >= 0)
                    tight.append(tighten(g[k]))
                assert_true(mccormick_cut(counts, s, g, Prover(tight^)))
                for r0 in range(7):
                    for r1 in range(7):
                        var rs = List[Int]([r0, r1])
                        if aff_eval(g[0], rs) < 0 or aff_eval(g[1], rs) < 0 or aff_eval(g[2], rs) < 0:
                            continue
                        var z2 = aff_eval(counts[3], rs)
                        var d = aff_eval(counts[0], rs) - aff_eval(counts[2], rs)
                        var f = z2 * (d - 1) - 2 * aff_eval(counts[2], rs) - d - 3 if s == 1 else z2 * (-d - 1) - 2 * aff_eval(counts[0], rs) + d + 3
                        assert_true(f >= 0)
    assert_true(carved > 20)


def test_bound_propagation_is_exact_on_integers() raises:
    """For systems of three forms a_0 + a_1 n_1 + a_2 n_2 (a_0 in -3..3,
    a_1, a_2 in -2..2; a deterministic stride through the triples), every
    point of [0, 8]^2 satisfying the system lies in the propagated box, and
    a system declared empty has no such point; some systems are empty only
    through three forms at once. search_point returns only satisfying points,
    finds one whenever [0, 7]^2 holds one, and declares empty only systems
    without a point; it proves a system empty that propagation does not."""
    var forms = _small_forms(-3, 3, 2)
    var n = len(forms)
    var empties = 0
    for i in range(0, n, 3):
        for j in range(i, n, 5):
            for k in range(j, n, 7):
                var sys = List[List[Int]]([forms[i].copy(), forms[j].copy(), forms[k].copy()])
                var box = propagate_bounds(sys, 2)
                if box.empty:
                    empties += 1
                var search = search_point(sys, 2)
                var found = search.point.copy()
                if search.empty:
                    assert_true(len(found) == 0)
                if len(found) > 0:
                    assert_true(aff_eval(sys[0], found) >= 0 and aff_eval(sys[1], found) >= 0 and aff_eval(sys[2], found) >= 0)
                for p0 in range(9):
                    for p1 in range(9):
                        var ns = List[Int]([p0, p1])
                        if aff_eval(sys[0], ns) < 0 or aff_eval(sys[1], ns) < 0 or aff_eval(sys[2], ns) < 0:
                            continue
                        assert_false(box.empty)
                        assert_false(search.empty)
                        if p0 < 8 and p1 < 8:
                            assert_true(len(found) > 0)
                        for t in range(2):
                            assert_true(ns[t] >= box.lo[t])
                            if box.bounded[t]:
                                assert_true(ns[t] <= box.hi[t])
    assert_true(empties > 100)
    # n_1 <= 0, n_2 <= 1 - n_1, n_2 >= 3 + n_1 - n_1: empty only via all three
    var three = List[List[Int]]([List[Int]([0, -1, 0]), List[Int]([1, -1, -1]), List[Int]([-3, 1, 1])])
    assert_true(propagate_bounds(three, 2).empty)
    # n_1 + n_2 = 1 and n_1 = n_2: the bounds [0, 1] never cross, but no
    # integer point exists; the exhaustive search proves it
    var half = List[List[Int]]([List[Int]([-1, 1, 1]), List[Int]([1, -1, -1]), List[Int]([0, 1, -1]), List[Int]([0, -1, 1])])
    assert_false(propagate_bounds(half, 2).empty)
    assert_true(search_point(half, 2).empty)


def test_bounded_z2_closes_for_every_delta() raises:
    """With Z_2 bounded, the tail is finitely many fully revealed run
    patterns symbolic in Delta: for s = +1, Z_2 <= 1, all 24 patterns close
    (every Delta >= 1); for s = -1, Z_2 <= 2, all 20 (every Delta <= 0)."""
    var p = zcap_cover(1, 1, 5000)
    assert_equal(p.patterns, 24)
    assert_equal(p.closed, 24)
    var m = zcap_cover(-1, 2, 5000)
    assert_equal(m.patterns, 20)
    assert_equal(m.closed, 20)


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
    test_pattern_refinement_partitions_the_word_pairs()
    print("[PASS] test_pattern_refinement_partitions_the_word_pairs")
    test_run_patterns_with_a_tail_close()
    print("[PASS] test_run_patterns_with_a_tail_close")
    test_the_residue_is_mostly_one_excursion()
    print("[PASS] test_the_residue_is_mostly_one_excursion")
    test_lemma_x_on_every_small_pair_of_monotone_paths()
    print("[PASS] test_lemma_x_on_every_small_pair_of_monotone_paths")
    test_crossing_closures_are_shared_tiles()
    print("[PASS] test_crossing_closures_are_shared_tiles")
    test_lemma_phi5_prime_the_short_suffix_of_w2()
    print("[PASS] test_lemma_phi5_prime_the_short_suffix_of_w2")
    test_reveal_census_needs_at_most_two_runs_to_length_7()
    print("[PASS] test_reveal_census_needs_at_most_two_runs_to_length_7")
    test_cover_pattern_closes_regions_by_lemma_x()
    print("[PASS] test_cover_pattern_closes_regions_by_lemma_x")
    test_impose_nonneg_partitions_exactly()
    print("[PASS] test_impose_nonneg_partitions_exactly")
    test_impose_equal_partitions_exactly()
    print("[PASS] test_impose_equal_partitions_exactly")
    test_guided_partition_closes_a_doubly_open_pattern()
    print("[PASS] test_guided_partition_closes_a_doubly_open_pattern")
    test_tighten_keeps_the_integer_points()
    print("[PASS] test_tighten_keeps_the_integer_points")
    test_the_prover_is_sound_on_its_regions()
    print("[PASS] test_the_prover_is_sound_on_its_regions")
    test_mccormick_quadrants_hold_no_pip_member()
    print("[PASS] test_mccormick_quadrants_hold_no_pip_member")
    test_bound_propagation_is_exact_on_integers()
    print("[PASS] test_bound_propagation_is_exact_on_integers")
    test_bounded_z2_closes_for_every_delta()
    print("[PASS] test_bounded_z2_closes_for_every_delta")
    require_contract("Theorem K's open family sigma(o) = y, sigma(y) = o w_1 o, sigma(z) = o w_2 o: det M = 2 (Z_1 - Z_2); the crossing test agrees with brute force; at |w_i| <= 5 there are 532 PIP members, Lemma Phi1 (w_1 begins with y) names verified level-2/3 paths on 274 and Lemma Phi2 (the Parikh walks of w_1 and w_2 + e_y cross) on 138, none failing, and the 120 non-crossing members are decided coincident at levels 3 to 6; an opaque-tail cone w_1 = y^(1+n) z T_1, w_2 = T_2 carries a level-3 path naming real shared tiles; the exploratory pattern tree at depth 6 has 14 certified, 8 empty, 19 Lemma P1 cut, 1 non-member and 34 open leaves, no closed leaf holds a PIP member it should not, and of the 532 members 413 lie in certified leaves (each at most the leaf level) and 119 in open ones; Lemma Phi4 (Pisot signs of Y_1 - Y_2 against Z_1 - Z_2) and Lemma Phi5 (the Z_1 = Z_2 + 1 non-crossing shape w_1 = u y^(Y_1 - Y_2), pi(u) = pi(w_2) + e_z) hold on all 2,136 members with |w_i| <= 6; at |w_i| <= 7 the Lemma Phi6-Phi8 paths verify on 1,180 of the 1,267 non-crossing members with none failing, the delta = e_z cell leaves only (zz, z) at level 6, (z, empty) is not PIP, and the other cells leave 87 members decided at levels 3 to 6; the run-shape cover: solve_constraint partitions the solutions of sum_pos n - sum_neg n = target exactly (every box solution hit once, targets -3..3), the quadratic Lemma P1 identities f(1) = Z_2 (Delta - 1) - 2 Y_2 - Delta - 3 (Z_1 = Z_2 + 1) and f(-1) = Z_2 (|Delta| - 1) - 2 Y_1 - |Delta| + 3 (Z_1 = Z_2 - 1) hold, a line-mode path (offsets affine along e_z - e_y) verifies on (z^a y^b, y^(b+1) z^(a+1)), a >= b + 2, and the shape cells (zy | eps), (zy | z), (zy | yz) with Z_1 = Z_2 + 1 close for Delta = 1, 2, 3 and the tail Delta >= 4 with no open region, while (zy | yz) with Z_1 = Z_2 - 1 closes at Delta = -1 using line mode; induction on runs: refining a run pattern's opaque tail (it ends, or one more run of the other letter and a new tail) partitions the word pairs (31 * 63 pairs with w_1 beginning with z, |w_i| <= 5, each in exactly one leaf), the patterns (zy | zy*), (zy | yz*), (zy* | z), (zy* | y), (zyz* | zy), (zyz* | yz), (z | z*), (z | y*), (z* | eps) -- the nine closed leaves of the run tree -- with Z_1 = Z_2 + 1, Delta = 1 close with no open region (each an infinite family with unboundedly many runs) while (zy* | zy*) does not at the same budget, and common points match their definition, 51 of the 87 residual members at |w_i| <= 7 having only t = 1; Lemma X (monotone lattice paths whose endpoints cross, or touch with a letter following, share a point) holds on every pair of paths of at most 4 steps, a weak end at a word end can leave the only shared point at the last level, the cone search closes 86 of the 87 residual members at |w_i| <= 7 by Lemma X, each confirmed by the exact level, Lemma Phi5' (Z_2 = Z_1 + 1, non-crossing: Delta <= 0, |w_2| = |w_1| + 1 - Delta, at least two z in the last 2 - Delta letters of w_2) holds on every member with |w_i| <= 7, the reveal census needs at most two revealed runs at longer-word lengths 5..7 (77/4, 255/13, 825/54), and cover_pattern certifies regions of zyz* y | zyz* by Lemma X; the certificate-guided partition: impose_nonneg covers {F >= 0} exactly (every form a_0 + a_1 n_1 + a_2 n_2, a_0 in -4..4, a_1, a_2 in -3..3, on the box [0, 5]^2) with F coefficientwise nonnegative on every region, impose_equal covers {E = 0} exactly (a_1, a_2 in -2..2, box [0, 6]^2), and cover_pattern_guided closes the doubly open pattern zy* y | zy* at Z_1 = Z_2 + 1, Delta = 1 with every carved region re-verified under its own inequalities; tighten keeps the integer points of every form a_0 + a_1 n_1 + a_2 n_2 (a_0 in -6..6, a_1, a_2 in -3..3) on [0, 6]^2, the Prover (affine, and quadratic U V + W) is sound under every pair of assumptions with coefficients in -1..1 on [0, 5]^2, and every McCormick quadrant of Lemma P1 that pisot_carve_forms opens in two-parameter families for s = +1 and s = -1 contains its point, passes mccormick_cut under its tightened forms, and holds no point with f < 0; integer bound propagation keeps every satisfying point of [0, 8]^2 in its box for a stride of three-form systems and declares empty only systems without one, and the exact point search returns only satisfying points, finds one whenever [0, 7]^2 holds one, and proves emptiness only of systems without a point; with Z_2 bounded the tails close for every Delta: s = +1, Z_2 <= 1 (24 fully revealed run patterns) and s = -1, Z_2 <= 2 (20)")
