"""Exact regressions for order-sensitive affine renewal ancestry."""

from std.testing import assert_equal, assert_true
from psc.affine_ancestry_trace import affine_ancestry_trace, common_terminal_trace_length, first_repeated_affine_state, same_affine_state
from psc.joint_local_type import same_joint_local_type
from psc.loop_quotient_census import addressed_samples_through_depth
from psc.words import Pair


def sigma() -> List[List[Int]]:
    var a0: List[Int] = [1]
    var a1: List[Int] = [0, 2, 1]
    var a2: List[Int] = [0, 0, 1]
    var out = List[List[Int]]()
    out.append(a0^)
    out.append(a1^)
    out.append(a2^)
    return out^


def seed_pair() -> Pair:
    var u: List[Int] = [0, 1]
    var v: List[Int] = [1, 0]
    return Pair(u, v)


def test_every_canonical_trace_closes() raises:
    var substitution = sigma()
    var samples = addressed_samples_through_depth(substitution, seed_pair(), 0, 7, 2, 1)
    assert_equal(len(samples), 601)
    for i in range(len(samples)):
        var trace = affine_ancestry_trace(substitution, samples[i].address)
        assert_equal(trace.depth(), samples[i].depth)
        assert_true(trace.closes())


def test_exact_sidewise_survivor_has_order_sensitive_trace() raises:
    var substitution = sigma()
    var samples = addressed_samples_through_depth(substitution, seed_pair(), 0, 7, 2, 1)
    var left = -1
    var right = -1
    for i in range(len(samples)):
        if samples[i].depth == 7 and samples[i].cut == 14:
            left = i
        elif samples[i].depth == 5 and samples[i].cut == 14:
            right = i
    assert_true(left >= 0)
    assert_true(right >= 0)
    assert_true(same_joint_local_type(samples[left].projection, samples[right].projection))
    var longer = affine_ancestry_trace(substitution, samples[left].address)
    var shorter = affine_ancestry_trace(substitution, samples[right].address)
    assert_equal(longer.depth(), 7)
    assert_equal(shorter.depth(), 5)
    # The prior abelian collision also shares its source affine state; only the
    # ordered intermediate trace can distinguish or expose a pump relation.
    assert_true(same_affine_state(longer, 0, shorter, 0))
    var terminal = common_terminal_trace_length(longer, shorter)
    print("[CALIBRATION] hard survivor common terminal affine states:", terminal)
    var repeated = first_repeated_affine_state(longer)
    print("[CALIBRATION] longer trace first repeated affine state:", repeated[0], repeated[1])


def main() raises:
    test_every_canonical_trace_closes()
    print("[PASS] test_every_canonical_trace_closes")
    test_exact_sidewise_survivor_has_order_sensitive_trace()
    print("[PASS] test_exact_sidewise_survivor_has_order_sensitive_trace")
    print("2 affine-ancestry-trace Mojo tests passed.")
