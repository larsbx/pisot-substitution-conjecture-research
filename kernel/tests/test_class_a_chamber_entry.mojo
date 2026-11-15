"""Exact regressions for the class-A chamber entry certificate.

docs/class-a-chamber-entry-stopgo-2026-11-15.md. Pinned here:

1. the cone engine's opt-in Bernstein rule: the middle coefficient is read with
   its denominators (a dip on a non-unit bracket reads negative); through the
   engine, a dip around beta refuses although both ends are positive, and on the
   sector cone the rule decides a sign that refuses without it;
2. Lemma TW over `Q[k, t]`: the chamber member `(3n - K, n, n - 1)` and its
   class-B twin have one incidence matrix, characteristic polynomial and left
   Perron vector (`ell (M - t I) = 0` mod chi), with `M g = -g - K e_y` and
   `(beta + 1) <ell, g> = -K ell_y` for `g = (1, 3, -6)`; their seed graphs differ;
3. the twelve families cover exactly `t <= 5` or `t <= k - 1` on
   `0 <= k, t <= 60` (the all-parameter proof is the note's §6.1), membership
   solved exactly far from the apex;
4. the transfer link (I2′): at six members the label set of the exact seed-patch
   graph equals that of the nine-seed closure in the oriented indexed graph
   `Gamma`, `Gamma = Reach(S9) ∪ R(Reach(S9))`, and every vertex of `Gamma`
   reaches an integral offset-zero vertex; at the sector apex the one vertex
   outside `Reach(S9)` is `R(E6) = (x, x, 0, -1, 0)`;
5. the line `t = 0` (Theorem L″'s line `A 2 2 1 0 1 -1`) is covered by the cone
   engine end to end: one symbolic region of 325 vertices, the count the Sturm
   line engine pins from `q0 = 107`, and 8 exact members.
"""

from std.collections import Dict
from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.param_poly import QX, TPoly, qx_affine2, qx_const, qx_key, tp_add, tp_at_q, tp_const, tp_deriv, tp_homog_at, tp_key, tp_mod_monic, tp_mul, tp_norm, tp_scale, tp_sub, tp_t
from psc.symbolic_cone import Bracket, Cone, Frac2, Region, bernstein_middle, certify_cone, r2_const
from psc.symbolic_line import Eventual, LineField
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_x_productivity import build_indexed, backwards, nine_sources
from psc.class_a_x_ladder import reversed_label
from psc.class_a_boundary_children import BoundaryLabel
from psc.pisot import CubicScreen
from a1_normal_form_census import CLASS_A, CLASS_B, class_member
from symbolic_line_certificate import exact_vertex_keys, same_set
from class_b_cone_certificate import Aff, CoverTally, Family, contains, cover, family_cone
from class_a_chamber_cone_certificate import chamber_families, chamber_member, coverage


def const_bracket(lo: Int, hi: Int) -> Bracket:
    return Bracket(r2_const(qx_const(lo)), r2_const(qx_const(hi)))


def middle(g: TPoly, br: Bracket) -> QX:
    return bernstein_middle(g, tp_homog_at(tp_deriv(g), br.lo.num, br.lo.den, 1), br)


def refuses(cone: Cone, g: TPoly, mut region: Region) -> Bool:
    """`sign_at_beta` raises for the stated reason, and for no other."""
    try:
        _ = cone.sign_at_beta(g, region)
    except e:
        return String(e).find("not decided on any bracket") >= 0
    return False


def test_bernstein_rule() raises:
    """`2 dL^2 dU b1` exactly. On [0, 4]: t^2 - 2t + 5 has b1 = 1 although it is
    neither monotone nor bending away there; (t - 1)(t - 3) is positive at both
    ends with b1 = -5. On [1/3, 3/2] (non-unit denominators, which pin the
    scaling): (3t - 4)(t - 1) is positive at both ends, dips inside, and has
    b1 = -11/12, read as 2 * 3^2 * 2 * b1 = -33."""
    var region = Region(0, 0)
    var br = const_bracket(0, 4)
    assert_equal(qx_key(middle(tp_norm([qx_const(5), qx_const(-2), qx_const(1)]), br)), qx_key(qx_const(2)))
    assert_equal(qx_key(middle(tp_norm([qx_const(3), qx_const(-4), qx_const(1)]), br)), qx_key(qx_const(-10)))
    var odd = Bracket(Frac2(qx_const(1), qx_const(3)), Frac2(qx_const(3), qx_const(2)))
    assert_equal(qx_key(middle(tp_norm([qx_const(4), qx_const(-7), qx_const(3)]), odd)), qx_key(qx_const(-33)))
    assert_equal(region.sign(middle(tp_norm([qx_const(4), qx_const(-7), qx_const(3)]), odd)), -1)


def test_bernstein_refuses_a_dip_at_beta() raises:
    """The member (k, t) = (8, 0), `(p, q, r) = (24, 11, 10)`, inside the certified
    region of the line t = 0 (Rouche certifies the disc there), beta = 13.21555...:
    `g = (10^4 t - 132155)(10^4 t - 132156)` is positive at both ends of both
    brackets and negative at beta, its leading coefficient has the end sign and
    its derivative changes sign on each bracket, so no rule may decide it; the
    Bernstein read is negative and the engine refuses."""
    var cone = family_cone(Family("(8,0)", Aff(24, 0, 0), Aff(11, 0, 0), Aff(10, 0, 0), 0, 0, CLASS_A))
    assert_true(cone.hull)
    var region = Region(0, 0)
    assert_true(certify_cone(cone, region).holds)
    var g = tp_norm([qx_const(17465076180), qx_const(-2643110000), qx_const(100000000)])
    var field = LineField(tp_at_q(cone.chi, 0, 0))
    var ev = Eventual()
    assert_equal(field.sign_at_beta(tp_at_q(g, 0, 0), ev), -1)
    for i in range(len(cone.brackets)):
        ref br = cone.brackets[i]
        assert_equal(region.sign(tp_homog_at(g, br.lo.num, br.lo.den, 2)), 1)
        assert_equal(region.sign(tp_homog_at(g, br.hi.num, br.hi.den, 2)), 1)
        assert_equal(region.sign(middle(g, br)), -1)
    assert_true(refuses(cone, g, region))


def sector() -> Family:
    return chamber_families()[6].copy()


def test_bernstein_decides_the_sector_sign() raises:
    """The element on which the sector cone stopped at s >= (2, 2) before the rule:
    lc = 4 - s1 changes sign on the region. With the rule its sign is -1, the exact
    sign at three members; the class-B twin's cone (same chi and brackets, rule
    off) refuses the same read."""
    var f = sector()
    assert_equal(f.name, "sector")
    var cone = family_cone(f)
    assert_true(cone.hull)
    var region = Region(2, 2)
    assert_true(certify_cone(cone, region).holds)
    var g = tp_norm([qx_affine2(-24, -4, -2), qx_affine2(-96, -8, -1), qx_affine2(4, 0, -1)])
    assert_equal(cone.sign_at_beta(g, region), -1)
    for pt in [(2, 2), (2, 9), (11, 2)]:
        var field = LineField(tp_at_q(cone.chi, pt[1], pt[0]))
        var ev = Eventual()
        assert_equal(field.sign_at_beta(tp_at_q(g, pt[1], pt[0]), ev), -1)
    var twin = family_cone(Family("sector-B", f.p.copy(), f.q.copy(), f.r.copy(), 0, 0, CLASS_B))
    assert_false(twin.hull)
    var plain = Region(2, 2)
    assert_true(certify_cone(twin, plain).holds)
    assert_true(refuses(twin, g, plain))


def chamber(cls: Int) raises -> Family:
    """The whole chamber as a cone family in `(s1, s2) = (k, t)`."""
    return Family("chamber", Aff(8, 2, 3), Aff(3, 1, 1), Aff(2, 1, 1), 0, 0, cls)


def test_lemma_tw_over_q_k_t() raises:
    var a = family_cone(chamber(CLASS_A))
    var b = family_cone(chamber(CLASS_B))
    # A = n + d = 3n - K, K = k + 1
    assert_equal(qx_key(a.run[0]), qx_key(qx_affine2(8, 3, 2)))
    for i in range(3):
        for j in range(3):
            assert_equal(qx_key(a.m[i][j]), qx_key(b.m[i][j]))
        assert_equal(tp_key(tp_norm(a.ell[i])), tp_key(tp_norm(b.ell[i])))
    var chi = tp_norm([qx_const(2), qx_affine2(-3, -1, 0), qx_affine2(-5, -1, -1), qx_const(1)])
    assert_equal(tp_key(tp_norm(a.chi)), tp_key(chi))
    assert_equal(tp_key(tp_norm(b.chi)), tp_key(chi))
    for j in range(3):  # ell is a left eigenvector: ell (M - t I) = 0 mod chi
        var col = TPoly()
        for i in range(3):
            var entry = tp_const(a.m[i][j])
            if i == j:
                entry = tp_sub(entry, tp_t())
            col = tp_add(col, tp_mul(a.ell[i], entry))
        assert_equal(len(tp_norm(tp_mod_monic(col, a.chi))), 0)
    var kk = qx_affine2(1, 0, 1)  # K
    var g = List[QX]([qx_const(1), qx_const(3), qx_const(-6)])
    var mg = a.mw(g)
    assert_equal(qx_key(mg[0]), qx_key(qx_const(-1)))
    assert_equal(qx_key(mg[1]), qx_key(qx_const(-3)))
    assert_equal(qx_key(mg[2]), qx_key(qx_affine2(5, 0, -1)))  # 6 - K
    var e = tp_add(tp_mul(a.t_of(g), tp_add(tp_t(), tp_const(qx_const(1)))), tp_scale(a.ell[2], kk))
    assert_equal(len(tp_norm(tp_mod_monic(e, a.chi))), 0)
    # the children differ: the seed graphs of the twins are not the same set
    for kt in [(0, 0), (12, 6)]:
        var m = chamber_member(kt[0], kt[1])
        assert_false(same_set(exact_vertex_keys(class_member(CLASS_A, m[0], m[1], m[2])), exact_vertex_keys(class_member(CLASS_B, m[0], m[1], m[2]))))


def find(fams: List[Family], name: String) raises -> Family:
    for i in range(len(fams)):
        if fams[i].name == name:
            return fams[i].copy()
    raise Error("no family ", name)


def member_of(f: Family, k: Int, t: Int) -> Bool:
    var m = chamber_member(k, t)
    return contains(f, m[0], m[1], m[2])


def test_decomposition() raises:
    var fams = chamber_families()
    assert_equal(len(fams), 12)
    var gaps = coverage(fams, 60)
    assert_equal(gaps[0], 0)  # every point with t <= 5 or t <= k - 1 is in a family
    assert_equal(gaps[1], 0)  # and no other point is
    assert_true(member_of(find(fams, "sector"), 1000, 500))
    assert_true(member_of(find(fams, "sector"), 12, 6))
    assert_false(member_of(find(fams, "sector"), 11, 6))
    assert_true(member_of(find(fams, "t=3"), 1000, 3))
    assert_true(member_of(find(fams, "k-t=3"), 1003, 1000))
    for i in range(len(fams)):
        assert_false(member_of(fams[i], 500, 500))  # D >= 2, t >= 6: not claimed


def label_key(w: BoundaryLabel) -> String:
    return String(w.top) + "|" + String(w.bottom) + "|" + String(w.x) + "," + String(w.c) + "," + String(w.y)


def test_transfer_link() raises:
    """The label set of `Reach_Gamma(S9)` is that of the exact seed-patch graph;
    `Gamma = Reach(S9) ∪ R(Reach(S9))` (both inclusions); every vertex of `Gamma`
    reaches `w = 0`. At the sector apex (12, 6) the graphs have 277 and 278
    vertices, the extra one `R(E6) = (x, x, 0, -1, 0)`."""
    for kt in [(0, 0), (0, 1), (1, 0), (2, 3), (3, 2), (12, 6)]:
        var k = kt[0]
        var t = kt[1]
        var m = chamber_member(k, t)
        var sigma = class_member(CLASS_A, m[0], m[1], m[2])
        var g = build_indexed(build_seed_overlap_tables_screened(sigma), k, t)
        var seen = List[Bool](length=len(g.states), fill=False)
        var queue = List[Int]()
        for w in nine_sources():
            var hit = -1
            for v in range(18):
                if g.states[v] == w:
                    hit = v
            assert_true(hit >= 0)
            if not seen[hit]:
                seen[hit] = True
                queue.append(hit)
        var cursor = 0
        while cursor < len(queue):
            var v = queue[cursor]
            cursor += 1
            for u in g.adj[v]:
                if not seen[u]:
                    seen[u] = True
                    queue.append(u)
        var keys = List[String]()
        var nine = Dict[String, Int]()
        for v in queue:
            keys.append(label_key(g.states[v]))
            nine[label_key(g.states[v])] = 1
        assert_true(same_set(keys, exact_vertex_keys(sigma)))
        var all = Dict[String, Int]()
        for v in range(len(g.states)):
            all[label_key(g.states[v])] = 1
        var zeros = List[Int]()
        var extra = List[String]()
        for v in range(len(g.states)):
            ref w = g.states[v]
            assert_true(label_key(w) in nine or label_key(reversed_label(w)) in nine)
            if label_key(w) in nine:
                assert_true(label_key(reversed_label(w)) in all)
            else:
                extra.append(label_key(w))
            if w.x == 0 and w.c == 0 and w.y == 0:
                zeros.append(v)
        var dist = backwards(g.adj, zeros)
        for v in range(len(dist)):
            assert_true(dist[v] >= 0)
        if k == 12 and t == 6:
            assert_equal(len(queue), 277)
            assert_equal(len(g.states), 278)
            assert_equal(len(extra), 1)
            assert_equal(extra[0], label_key(BoundaryLabel(0, 0, 0, -1, 0)))


def test_line_t0_end_to_end() raises:
    var screen = CubicScreen()
    var tally = CoverTally()
    cover(find(chamber_families(), "t=0"), screen, tally)
    assert_equal(tally.non_pip, 0)
    assert_equal(tally.regions, 1)
    assert_equal(tally.finite, 8)
    assert_equal(tally.largest, 325)  # the symbolic count pinned for `A 2 2 1 0 1 -1` (kernel/symbolic_line_pins.txt)


def main() raises:
    test_bernstein_rule()
    print("[PASS] test_bernstein_rule")
    test_bernstein_refuses_a_dip_at_beta()
    print("[PASS] test_bernstein_refuses_a_dip_at_beta")
    test_bernstein_decides_the_sector_sign()
    print("[PASS] test_bernstein_decides_the_sector_sign")
    test_lemma_tw_over_q_k_t()
    print("[PASS] test_lemma_tw_over_q_k_t")
    test_decomposition()
    print("[PASS] test_decomposition")
    test_transfer_link()
    print("[PASS] test_transfer_link")
    test_line_t0_end_to_end()
    print("[PASS] test_line_t0_end_to_end")
    require_contract("class-A chamber entry: the cone engine's opt-in Bernstein rule reads 2 dL^2 dU b1 exactly (non-unit brackets included), decides a quadratic whose leading coefficient changes sign on the region, and refuses through the engine a dip around beta with positive ends; Lemma TW over Q[k, t] (one incidence matrix, chi = l^3 - (n + 2) l^2 - (t + 3) l + 2 and left eigenvector ell (M - t I) = 0 mod chi for the class-A chamber member and its class-B twin, M g = -g - K e_y and (beta + 1) <ell, g> = -K ell_y for g = (1, 3, -6)), the twins' seed graphs differing; the twelve families cover exactly t <= 5 or t <= k - 1 on 0 <= k, t <= 60; at six members the exact seed-patch graph and the nine-seed closure in the oriented indexed graph have one label set, the graph is that closure with its reversal (both inclusions), the apex's one extra vertex is R(E6), and every vertex reaches integral offset zero; the line t = 0 covered by the cone engine with one 325-vertex region and 8 exact members")
