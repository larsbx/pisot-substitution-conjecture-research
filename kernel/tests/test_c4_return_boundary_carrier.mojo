"""Exact complete carrier and word-register controls; no finite-C4 promotion."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution
from psc.words import parikh
from psc.c4_return_boundary_carrier import ReturnBoundaryCarrier


def _prefix(w: List[Int], n: Int) -> List[Int]:
    var out = List[Int]()
    for i in range(n):
        out.append(w[i])
    return out^


def test_all_28_states_and_80_actual_child_occurrences() raises:
    var c = ReturnBoundaryCarrier()
    var lifted = c.lifted_images()
    assert_equal(len(lifted), 28)
    var count = 0
    for j in range(4):
        var flattened = List[Int]()
        for d in range(len(c.words[j])):
            var source_prefix = _prefix(c.words[j], d)
            var expanded_prefix = apply_substitution(c.sigma, source_prefix)
            var image = c.sigma[c.words[j][d]].copy()
            var id = c.point_id(j, d)
            assert_equal(len(lifted[id]), len(image))
            for t in range(len(image)):
                var e = c.edge(j, d, t)
                assert_equal(e.child, t)
                assert_equal(e.target_return, c.tau[j][e.occurrence])
                assert_equal(e.emitted, _prefix(c.tau[j], e.occurrence))
                var left = expanded_prefix.copy()
                for i in range(t):
                    left.append(image[i])
                var right = c.decode(e.emitted)
                for i in range(e.target_offset):
                    right.append(c.words[e.target_return][i])
                assert_equal(left, right)
                assert_equal(image[t], c.words[e.target_return][e.target_offset])
                var target = c.point_id(e.target_return, e.target_offset)
                assert_equal(lifted[id][t], target)
                flattened.append(target)
                count += 1
        # Literal Lambda H(j) = H tau(j); includes repeated occurrences.
        var expected = List[Int]()
        for symbol in c.tau[j]:
            for d in range(len(c.words[symbol])):
                expected.append(c.point_id(symbol, d))
        assert_equal(flattened, expected)
    assert_equal(count, 80)


def test_external_prefix_transport_and_inherited_cycles() raises:
    var c = ReturnBoundaryCarrier()
    var basin: List[Int] = [0, 0, 0]
    var exterior: List[List[Int]] = [[], [0], [3, 2]]
    for j in range(4):
        for d in range(len(c.words[j])):
            for t in range(len(c.sigma[c.words[j][d]])):
                var e = c.edge(j, d, t)
                for u in exterior:
                    var source = c.decode(u)
                    for i in range(d):
                        source.append(c.words[j][i])
                    var left = apply_substitution(c.sigma, source)
                    for i in range(t):
                        left.append(c.sigma[c.words[j][d]][i])
                    var output = c.tau_apply(u)
                    for a in e.emitted:
                        output.append(a)
                    var right = c.decode(output)
                    for i in range(e.target_offset):
                        right.append(c.words[e.target_return][i])
                    assert_equal(left, right)
            var a = j
            var p = d
            for _ in range(3):
                var e = c.edge(a, p, 0)
                a = e.target_return
                p = e.target_offset
            var again = c.edge(a, p, 0)
            assert_equal(again.target_return, a)
            assert_equal(again.target_offset, p)
            if a == 0 and p == 0:
                basin[0] += 1
            elif a == 1 and p == 6:
                basin[1] += 1
            else:
                assert_equal(a, 2)
                assert_equal(p, 3)
                basin[2] += 1
    assert_equal(basin, [12, 8, 8])
    var initial = c.edge(0, 5, 0)
    var recurring = c.edge(1, 6, 0)
    assert_equal(initial.emitted, [0])
    assert_equal(initial.occurrence, 1)
    assert_equal(recurring.emitted, [3, 2])
    assert_equal(recurring.occurrence, 2)
    assert_equal(initial.target_return, 1)
    assert_equal(initial.target_offset, 6)
    assert_equal(recurring.target_return, 1)
    assert_equal(recurring.target_offset, 6)


def test_two_phase_register_identities_through_depth_six() raises:
    var c = ReturnBoundaryCarrier()
    for kind in range(2):
        for n in range(7):
            var r = c.residual(n, kind)
            var a = 0
            var b = 3
            if kind == 1:
                a = 1
                b = 2
            assert_equal(r.longer, c.code_image(a, n))
            assert_equal(r.shorter, c.code_image(b, n))
            var expected_tail: List[Int] = [1]
            for _ in range(n + 1):
                expected_tail = apply_substitution(c.sigma, expected_tail)
            var actual_tail: List[Int] = [1, 2, 1]
            var full_returns = c.decode(r.tail)
            for x in full_returns:
                actual_tail.append(x)
            assert_equal(actual_tail, expected_tail)
            var expected_longer = c.decode(r.shorter)
            for x in actual_tail:
                expected_longer.append(x)
            assert_equal(c.decode(r.longer), expected_longer)
            if r.phase == 1:
                assert_equal(r.longer[len(r.common)], 1)
                assert_equal(r.shorter[len(r.common)], 2)


def test_identical_local_states_do_not_establish_a_balanced_cut() raises:
    var c = ReturnBoundaryCarrier()
    var empty_prefix = _prefix(c.words[1], 6)
    var extra_return = c.words[0].copy()
    for x in empty_prefix:
        extra_return.append(x)
    var a = parikh(empty_prefix)
    var b = parikh(extra_return)
    assert_equal([a[0]-b[0], a[1]-b[1], a[2]-b[2]], [-1, -5, -2])
    assert_true(a != b)
    # Both next letters are literally the same state (1,6), yet not balanced.
    assert_equal(c.words[1][6], 1)


def test_bad_addresses_and_materialization_caps_refuse() raises:
    var c = ReturnBoundaryCarrier()
    var bad: List[List[Int]] = [[-1,0,0],[4,0,0],[0,-1,0],[0,8,0],[0,0,-1],[0,0,2],[1,6,3]]
    for v in bad:
        var refused = False
        try:
            _ = c.edge(v[0], v[1], v[2])
        except:
            refused = True
        assert_true(refused)
    for n in [-1, 7, 1000000]:
        var refused = False
        try:
            _ = c.residual(n, 0)
        except:
            refused = True
        assert_true(refused)
    for kind in [-1, 2]:
        var refused = False
        try:
            _ = c.residual(0, kind)
        except:
            refused = True
        assert_true(refused)
    var refused_code = False
    try:
        _ = c.decode([4])
    except:
        refused_code = True
    assert_true(refused_code)


def main() raises:
    test_all_28_states_and_80_actual_child_occurrences()
    test_external_prefix_transport_and_inherited_cycles()
    test_two_phase_register_identities_through_depth_six()
    test_identical_local_states_do_not_establish_a_balanced_cut()
    test_bad_addresses_and_materialization_caps_refuse()
    print("28 return-cut states; 80 ordered child edges; exact two-phase residual registers passed")
    require_contract("exact #487 return-cut refinement retains all 80 child occurrences on 28 local states and satisfies both literal intertwining identities; two-phase word-register residuals are exact, but their unbounded words and two-track Parikh differences are not a finite C4 proof")
