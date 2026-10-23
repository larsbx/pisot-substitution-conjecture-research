"""Boundary hitting on class-A residue rays (n+d, n, n+eps), n = d l + r: certificate and refusals."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_a_line import ALine
from psc.class_a_line_graph import survey
from psc.class_a_gap_four_rank_tables import tabulated_rays, ray_tables, certify_ray
from psc.class_a_typed_carrier import certify_finite_line
from psc.class_a_carrier_closure import certify_closure_line, check_line_identity, a_div_ceil, a_div_floor
from psc.class_a_carrier_descent import certify_descent_line, replay_descent_finite_line
from a1_normal_form_census import CLASS_A, class_member
from symbolic_line_certificate import exact_hits


def refuses_closure(line: ALine, n0: Int, rows: List[List[Int]]) -> Bool:
    try:
        _ = certify_closure_line(line, n0, rows)
        return False
    except:
        return True


def refuses_descent(line: ALine, n0: Int, rows: List[List[Int]], pieces: List[List[Int]],
                    descents: List[List[Int]]) -> Bool:
    try:
        _ = certify_descent_line(line, n0, rows, pieces, descents)
        return False
    except:
        return True


def main() raises:
    # Exact ceil/floor division of affine forms by the gap; a slope not divisible refuses.
    assert_equal(a_div_ceil([4, -3], 2), List[Int]([2, -1]))
    assert_equal(a_div_floor([4, -3], 2), List[Int]([2, -2]))
    assert_equal(a_div_ceil([-6, 7], 3), List[Int]([-2, 3]))
    var refused = False
    try:
        _ = a_div_floor([3, 0], 2)
    except:
        refused = True
    assert_true(refused)
    # A residue outside 0..d-1 and a parameter off its ray refuse.
    refused = False
    try:
        check_line_identity(ALine(2, -1, 2))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = ALine(2, -1, 0).l_of(15)
    except:
        refused = True
    assert_true(refused)
    var rays = tabulated_rays()
    for spec in rays:
        var line = ALine(spec[0], spec[1], spec[2])
        var n0 = spec[3]
        var t = ray_tables(line)
        # The uniform certificate on the whole ray n >= n0.
        _ = certify_ray(line, n0)
        # Every n of the line below the floor is an exact complete graph that hits.
        for n in range(1, n0):
            if n % line.d == line.r and line.d <= 2 * n + 6 * line.eps + 5:
                _ = survey(line, n)
        # Carrier = graph label set, with the independent cardinality, and
        # differential replay of every chosen occurrence, at the first two members.
        for m in range(2):
            var n = line.n_of(line.l_of(n0 + (line.d - (n0 - line.r) % line.d) % line.d) + m)
            _ = certify_finite_line(line, n, t[0], spec[4], spec[5])
            _ = replay_descent_finite_line(line, n, t[0], t[1], t[2], spec[4], spec[5])
        # Negative controls: a removed row escapes; the other residue's carrier
        # and the gap-one carrier do not fit; damaged descents refuse.
        var damaged = List[List[Int]]()
        for i in range(1, len(t[0])):
            damaged.append(t[0][i].copy())
        assert_true(refuses_closure(line, n0, damaged))
        if line.d > 1:
            var other = ALine(line.d, line.eps, (line.r + 1) % line.d)
            assert_true(refuses_closure(line, n0, ray_tables(other)[0]))
        var raised = t[1].copy()
        raised[t[2][0][8]][7] += 50
        assert_true(refuses_descent(line, n0, t[0], raised, t[2]))
        var mislabelled = t[2].copy()
        mislabelled[0][7] += 1
        assert_true(refuses_descent(line, n0, t[0], t[1], mislabelled))
        var fewer = List[List[Int]]()
        for i in range(1, len(t[2])):
            fewer.append(t[2][i].copy())
        assert_true(refuses_descent(line, n0, t[0], t[1], fewer))
        if line.d == 4:
            var illegal = t[2].copy()
            illegal[0][5] = 3  # only first/run/last parts 0,1,2 exist
            assert_true(refuses_descent(line, n0, t[0], t[1], illegal))
            assert_true(refuses_closure(line, n0 - 4, t[0]) or
                        refuses_descent(line, n0 - 4, t[0], t[1], t[2]))
    # Preserve the original certificate's separate exact n=0 check, even
    # though main's ALine now admits this member directly.
    var zero = exact_hits(class_member(CLASS_A, 4, 0, 1))
    assert_true(zero > 0)
    print("CLASS_A_GAP_FOUR_ZERO_MEMBER vertices=", zero, "all_hit=true")
    require_contract("alternative class-A gap-four rank tables from #326: residue rays n = d l + r of (n+d,n,n+eps): uniform forward closure of l-affine typed carriers and strict descent of l-affine potentials by exact Sturm signs on (0,1/n0], per tabulated ray from its floor; complete graphs below every floor and d=4 plus n=0; carrier = graph label set with independent cardinality and differential replay at two members; removed row, other residue's carrier, raised potential, mislabelled and missing descents refuse; untabulated rays, other A/C regions and universal #139 open")
