"""All-parameter rank conditions, their negative controls, and a native finite replay."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_b_rank_certificate import RankCertificate, check_rank_certificate, child_label
from class_b_rank_certificate import replay
from class_b_label_rays import label_block

# One type, k in [-t-2,-1] u {0} u [1,t+2], X = |k|. The two wings swap with
# k -> -1-k and k -> 1-k, a translation by 2 per lap, and enter k=0 at |k|=1.
comptime TOY = """C plus 1 0 1
P 0 1 0 0 -1 -2 0 -1 0 -1 0 0
P 0 1 0 0 0 0 0 0 0 0 0 1
P 0 1 0 0 0 1 1 2 0 1 0 0
E 0 1 -1 0 -1 0 -1
E 0 2 -1 -1 -2 0 -2
E 2 1 1 0 1 0 1
E 2 0 1 0 2 1 2
"""


def refuses(text: String, reason: String) -> Bool:
    try:
        _ = check_rank_certificate(RankCertificate(text))
    except e:
        return reason in String(e)
    return False


def main() raises:
    var toy = String(TOY)
    assert_equal(check_rank_certificate(RankCertificate(toy)), 1)
    # Negative controls: each tampering breaks exactly the condition it names.
    assert_true(refuses(toy.replace("P 0 1 0 0 0 1 1 2 0 1 0 0", "P 0 1 0 0 0 1 1 2 0 1 -1 0"), "does not decrease at an edge vertex"))
    assert_true(refuses(toy.replace("P 0 1 0 0 0 1 1 2 0 1 0 0", "P 0 1 0 0 0 1 1 2 1 0 0 0"), "does not decrease along an edge ray"))
    assert_true(refuses(toy.replace("E 2 1 1 0 1 0 1\n", ""), "uncovered"))
    assert_true(refuses(toy.replace("E 2 0 1 0 2 1 2", "E 2 0 -1 0 2 1 2"), "image leaves"))
    assert_true(refuses(toy.replace("P 0 1 0 0 -1 -2 0 -1 0 -1 0 0", "P 0 1 0 0 -1 -2 0 -1 0 -1 -2 0"), "negative potential"))
    assert_true(refuses(toy.replace("P 0 1 0 0 0 0 0 0 0 0 0 1", "P 0 1 0 0 0 0 0 0 0 0 0 0"), "without a descent edge"))
    # The committed plus g=1 certificate, and its replay on the native q=10 export.
    var text: String
    with open("../evidence/class-b-rank-certificate-2026-10-27/plus-g1-r0.cert", "r") as f:
        text = f.read()
    var cert = RankCertificate(text)
    _ = check_rank_certificate(cert)
    var export = label_block(True, 1, 10, 20000, False, True)
    assert_true(replay(cert, export).startswith("RANK_REPLAY_PASS q 10 vertices 2877 edges_checked 2869 "))
    # Deleting the actual graph edge behind one chosen symbolic edge must refuse.
    ref e = cert.edges[0]
    ref p = cert.pieces[e.parent]
    var k = e.lo.at(0)
    var parent: List[Int] = [p.top, p.bottom, k, 3 * k + p.d, p.s - 6 * k - p.d]
    var line = String("E")
    for x in parent:
        line += " " + String(x)
    for x in child_label(cert, 0, k):
        line += " " + String(x)
    assert_true(line + "\n" in export)
    var refused = False
    try:
        _ = replay(cert, export.replace(line + "\n", ""))
    except err:
        refused = "not an actual edge" in String(err)
    assert_true(refused)
    require_contract("class B piecewise rank certificate: vertex/ray descent and nonnegativity, exact coverage sweep past every crossing, negative controls refuse, native q=10 replay; conditional on carrier inclusion and actual symbolic edges")
