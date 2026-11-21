from std.sys import argv
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_marker_reachability import (
    MarkerRegister, MarkerRegisterTable, NO_LAST, PHASES, Seam, SeamPair,
    decide_marker_ray, verify_marker_certificate,
)
from psc.symmetry import word_key
from substitution_dynamics.substitution import Substitution
from substitution_dynamics.symmetry import parse_substitution_key


def family(n: Int, reordered: Bool = False) -> List[List[Int]]:
    var a: List[Int] = [0, 1, 2, 0] if reordered else [0, 2, 1, 0]
    var b: List[Int] = [1, 2, 0, 1]
    var c: List[Int] = [0, 1]
    a.extend(List[Int](length=n + 1, fill=0))
    a.extend(List[Int](length=n + 3, fill=1))
    a.extend(List[Int](length=n + 3, fill=2))
    a.append(0)
    b.extend(List[Int](length=n + 1, fill=1))
    b.extend(List[Int](length=n + 4, fill=0))
    b.extend(List[Int](length=n + 3, fill=2))
    b.append(1)
    c.extend(List[Int](length=n + 3, fill=0))
    c.extend(List[Int](length=n + 3, fill=1))
    c.extend(List[Int](length=n + 4, fill=2))
    c.append(1)
    return [a^, b^, c^]


def _family_and_reorder() raises:
    var pair = SeamPair(Seam(0, 0), Seam(0, 0), Seam(1, 1))
    for n in [0, 2]:
        var hit = decide_marker_ray(family(n), pair).violation.value().copy()
        assert_equal(word_key(hit.top_word), "021")
        assert_equal(word_key(hit.bottom_word), "120")
        assert_equal(hit.top_next, 0)
        assert_equal(hit.bottom_next, 1)
        assert_equal(hit.balance, [1, 1, 1])
        assert_equal(hit.top_markers, 1)
        assert_equal(hit.bottom_markers, 0)
        assert_equal(hit.required_parity, 0)
        assert_true(not hit.same_last_group and not hit.same_next_group)
        assert_equal(hit.top_path, [0, 0, 0, 0, 0, 3])
        assert_equal(hit.bottom_path, hit.top_path)
    var reordered = family(0, reordered=True)
    var right = decide_marker_ray(reordered, pair).violation.value().copy()
    assert_equal(len(right.top_word), 25)
    assert_true(right.same_last_group and not right.same_next_group)
    var left = decide_marker_ray(reordered, pair, leftward=True).violation.value().copy()
    assert_true(left.leftward)
    assert_equal(word_key(left.top_word), "02221")
    assert_equal(word_key(left.bottom_word), "12220")
    assert_true(not left.same_last_group and not left.same_next_group)
    assert_equal(left.top_markers, 0)
    assert_equal(left.bottom_markers, 1)
    print("family t=4,6: parity violations at length 3")
    print("reordered t=4: right same-last-group at length 25; left parity at length 5")


def _cycling_endpoints() raises:
    var sigma = parse_substitution_key("01/112/021", 3)
    var pair = SeamPair(Seam(1, 0), Seam(1, 0), Seam(2, 1))
    var hit = decide_marker_ray(sigma, pair).violation.value().copy()
    assert_equal(word_key(hit.top_word), "01112112112")
    assert_equal(word_key(hit.bottom_word), "11211202111")
    assert_equal(hit.balance, [1, 7, 3])
    assert_true(not hit.same_last_group and hit.same_next_group)
    print("01/112/021: right same-next-group at length 11")


def _thue_morse() raises:
    for key in ["01/10", "0110/1001"]:
        var sigma = parse_substitution_key(key, 2)
        # Both choices are legal and opposite. The second starts in the
        # non-marker first group on the right, exercising that initial bit.
        for pair in [
            SeamPair(Seam(0, 0), Seam(0, 0), Seam(1, 1)),
            SeamPair(Seam(0, 0), Seam(0, 1), Seam(1, 0)),
        ]:
            for side in [False, True]:
                var result = decide_marker_ray(sigma, pair, leftward=side)
                assert_true(not result.violation)
                assert_true(verify_marker_certificate(sigma, pair, side, result.certificate))
                assert_true(len(result.certificate) <= 1728 * result.parikh_states + 1)
                var incomplete = result.certificate.copy()
                _ = incomplete.pop()
                assert_true(not verify_marker_certificate(sigma, pair, side, incomplete))
                print(key, pair.top.right, side, "Parikh", result.parikh_states,
                      "certificate", len(result.certificate))


def _refusals() raises:
    var pair = SeamPair(Seam(0, 0), Seam(0, 0), Seam(1, 1))
    var sigma = family(0)
    var refused = False
    try:
        _ = decide_marker_ray(sigma, pair, state_cap=1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = decide_marker_ray(sigma, pair, literal_cap=2)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = decide_marker_ray(sigma, SeamPair(pair.marker.copy(), pair.top.copy(), Seam(0, 1)))
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = MarkerRegisterTable(Substitution.checked([[0, 0, 1], [1, 1, 0]]), pair.marker)
    except:
        refused = True
    assert_true(refused)


def _trace(tag: String, images: List[List[Int]], marker: Seam) raises:
    var table = MarkerRegisterTable(Substitution.checked(images), marker)
    for phase in range(PHASES):
        for a in range(len(images)):
            for d in range(len(images[a])):
                for previous in range(NO_LAST + 1):
                    if previous < NO_LAST and previous >= len(images):
                        continue
                    for parity in range(2):
                        var x = table.advance(phase, MarkerRegister(previous, NO_LAST, parity), a, 0, d, 0)
                        var y = table.advance(phase, MarkerRegister(NO_LAST, previous, parity), 0, a, 0, d)
                        print(tag, phase, a, d, previous, parity, x.top_last, x.bottom_last,
                              x.parity, y.top_last, y.bottom_last, y.parity)


def main() raises:
    var args = argv()
    if len(args) == 2 and args[1] == "--trace":
        _trace("family", family(0), Seam(0, 0))
        _trace("cycling", parse_substitution_key("01/112/021", 3), Seam(1, 0))
        _trace("thue-morse", parse_substitution_key("01/10", 2), Seam(0, 0))
        return

    _family_and_reorder()
    _cycling_endpoints()
    _thue_morse()
    _refusals()
    require_contract("The exact Parikh automaton and six-phase marker product decide balanced periodic seam prefixes, with literal target replay or a checked closed certificate. Reversal tests the other ray. Positive controls include parity and endpoint violations, and Thue-Morse certifies both directions.")
