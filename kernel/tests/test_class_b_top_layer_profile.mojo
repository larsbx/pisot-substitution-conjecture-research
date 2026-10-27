"""Class B top-layer profile: window, Theorem C disjointness, pinned counts, refusals."""
from std.testing import assert_true, assert_false, assert_equal
from mojo_smoke.claims import require_contract
from class_b_top_layer_profile import in_open_top_layer, label_fit, profile, top_layer_member
from lateral_conjugacy_census import theorem_c_region


def main() raises:
    # The open window and Theorem C's region are disjoint on both branches.
    for plus in [True, False]:
        for q in range(1, 41):
            for d in range(0, 20):
                var t = top_layer_member(plus, d, q)
                if t[2] >= 0 and in_open_top_layer(plus, t[0], q):
                    assert_false(theorem_c_region(t[0], t[1], t[2]))
    # d is the distance to the Pisot boundary p < 3q + 12 (plus), p < 3q (minus).
    assert_equal(top_layer_member(True, 0, 10)[0], 3 * 10 + 11)
    assert_equal(top_layer_member(False, 0, 10)[0], 3 * 10 - 1)

    # Pinned finite counts: minus d = 2, every vertex hits offset zero (profile raises otherwise).
    var pts = profile(False, 2, 13)
    assert_equal(len(pts), 3)
    assert_equal(pts[0].q, 11)
    assert_equal(pts[0].vertices, 584)
    assert_equal(pts[1].vertices, 574)
    assert_equal(pts[2].vertices, 734)

    # Step 1 on the smallest window: plus g = 1, q <= 11. In the (u, v) basis the
    # typed rows are affine in q from q = 9 on, with 389 rows.
    var fit = label_fit(True, 0, 11)
    assert_equal(len(fit), 1)
    assert_equal(fit[0][2], 9)
    assert_equal(fit[0][3], 389)

    var refused = False
    try:
        _ = profile(True, 0, 49)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = profile(True, -1, 5)
    except:
        refused = True
    assert_true(refused)
    require_contract("class B top-layer probe: the open window p = 3q+11-d (plus) / 3q-1-d (minus) is disjoint from Theorem C's region; complete uncapped seed graphs on minus d=2, q=11..13 have 584, 574, 734 vertices and every vertex hits offset zero; on plus g=1, q<=11, the (u,v)-basis typed k-intervals are affine in q from q=9 (389 rows); bounds refuse; exploratory, not a certificate")
