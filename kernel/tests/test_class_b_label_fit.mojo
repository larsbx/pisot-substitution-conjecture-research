"""Finite affine labels, count-only false positives, and export refusals."""
from std.testing import assert_true, assert_false, assert_equal
from mojo_smoke.claims import require_claim, require_contract
from psc.class_b_label_fit import affine_equal, tail_partition_ok
from class_b_label_rays import label_block
from psc.class_b_ray_carrier import prefix, child_coordinates
from class_b_top_layer_profile import top_layer_member
from a1_normal_form_census import CLASS_B, class_member
from psc.bpa import substitution_incidence
from finite_linear_algebra.mat3 import Mat3


def main() raises:
    var a = List[List[Int]]()
    var b = List[List[Int]]()
    var c = List[List[Int]]()
    a.append([0, 1, 1, 2, 1, 2])
    b.append([0, 1, 1, 2, 1, 3])
    c.append([0, 1, 1, 2, 1, 4])
    assert_true(affine_equal(a, b, c, 2))
    assert_true(tail_partition_ok(a, b))
    var shrinking = List[List[Int]]()
    shrinking.append([0, 1, 1, 2, 1, 1])
    assert_false(tail_partition_ok(a, shrinking))
    var separating_a = List[List[Int]]()
    var separating_b = List[List[Int]]()
    separating_a.append([0, 1, 1, 2, 0, 1])
    separating_a.append([0, 1, 1, 2, 5, 6])
    separating_b.append([0, 1, 1, 2, 0, 2])
    separating_b.append([0, 1, 1, 2, 5, 6])
    assert_false(tail_partition_ok(separating_a, separating_b))
    c[0][4] = 2
    c[0][5] = 5  # Same size, different labels.
    assert_false(affine_equal(a, b, c, 2))
    c[0][4] = 1
    c[0][5] = 4
    c[0][3] = 3
    assert_false(affine_equal(a, b, c, 2))
    assert_false(affine_equal(a, b, c, 1))
    for cap in [0, 1, 20001]:
        var refused = False
        try:
            _ = label_block(False, 3, 11, cap)
        except:
            refused = True
        assert_true(refused)
    var text = label_block(False, 3, 11)
    assert_true(text.startswith("M 11 584 5\n"))
    # Compare symbolic coordinate identities against direct incidence and actual prefixes.
    for plus in [True, False]:
        var q = 12
        var t = top_layer_member(plus, 2, q)
        var sigma = class_member(CLASS_B, t[0], q, t[2])
        var matrix = Mat3(substitution_incidence(sigma))
        for top in range(3):
            for bottom in range(3):
                for i in range(len(sigma[top])):
                    for j in [0, 1, len(sigma[bottom]) - 1]:
                        var pa = List[Int]([0, 0, 0])
                        var pb = List[Int]([0, 0, 0])
                        for z in range(i):
                            pa[sigma[top][z]] += 1
                        for z in range(j):
                            pb[sigma[bottom][z]] += 1
                        assert_equal(prefix(plus, 3, q, top, i), pa)
                        var s = 2
                        var d = -1
                        var k = 3
                        var direct = matrix.apply([k, 3 * k + d, s - 6 * k - d])
                        for z in range(3):
                            direct[z] += pb[z] - pa[z]
                        var typed = child_coordinates(plus, 3, q, s, d, k, top, bottom, i, j)
                        assert_equal(typed[0], 3 * direct[0] + direct[1] + direct[2])
                        assert_equal(typed[1], direct[1] - 3 * direct[0])
                        assert_equal(typed[2], direct[0])
    var illegal = False
    try:
        _ = prefix(True, 3, 12, 0, -1)
    except:
        illegal = True
    assert_true(illegal)
    var with_witnesses = label_block(False, 3, 11, 20000, True)
    var witness_count = 0
    for line in with_witnesses.splitlines():
        if line.startswith("W "):
            witness_count += 1
    assert_true(witness_count > 500)
    require_contract("class B finite label intervals: direction (1,3,-6), exact endpoint comparisons, equal-count/different-label negative controls, caps refuse; no uniform certificate")
    require_claim("ClassBTopLayerLabelRays")
