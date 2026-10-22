"""Class-A d=2 plus line (n+2,n,n+1): the assembled theorem and its shown witnesses."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_d2_plus_line import d2p, hand_step, ray_spec, theorem, witness
from psc.class_a_d2_parity_carrier import inferred_template
from psc.class_a_ray_tables import ray_tables
from psc.overlap_seed_patch import build_seed_overlap_tables_screened


def refuses_witness(n: Int) -> Bool:
    try:
        _ = witness(n, False)
    except:
        return True
    return False


def refuses_step(sigma: List[List[Int]], n: Int, record: List[Int]) -> Bool:
    try:
        hand_step(sigma, n, record)
    except:
        return True
    return False


def main() raises:
    theorem()
    # Witnesses at the first and last replayable members of both rays.
    for n in [13, 14, 15, 23, 24]:
        var spec = ray_spec(n % 2)
        var l = n // 2
        var shown = witness(n, False)
        assert_equal(shown[0], spec[4] * l + spec[5])   # labels = carrier cardinality = graph size
        assert_equal(shown[1], 8)                        # offset-zero targets
        assert_equal(shown[2], 9)                        # canonical swap seeds, all in the carrier
        assert_true(shown[4] <= 2 * l + (9 if n % 2 == 0 else 11))
    # The hand derivation pins x y^(n+2) x at n=14: from (x,x,0,1,-2), occurrence
    # (0,17) is the final x of the bottom image; the child is (x,x,0,-1,0).
    var sigma = build_seed_overlap_tables_screened(d2p(0).member(14)).sigma.copy()
    var good: List[Int] = [0, 0, 0, 1, -2, 0, 9, 0, 17, 0, 0, 0, -1, 0, 6]
    hand_step(sigma, 14, good)
    for at in [9, 10, 11, 12, 13]:
        var bad = good.copy()
        bad[at] += 1
        assert_true(refuses_step(sigma, 14, bad))
    var shifted = good.copy()
    shifted[8] = 16
    assert_true(refuses_step(sigma, 14, shifted))
    # Below a floor the witness defers to the exact graph; a third residue does not exist.
    assert_true(refuses_witness(12))
    assert_true(refuses_witness(11))
    var refused = False
    try:
        _ = d2p(2)
    except:
        refused = True
    assert_true(refused)
    # The template identity is residue-sensitive.
    assert_true(len(ray_tables(d2p(0))[0]) != len(inferred_template(9, 13)))
    require_contract("class-A d=2 plus line (n+2,n,n+1): boundary hitting for every n>=1 assembled from exact complete graphs n=1..12 and the residue-ray certificate on n=2l (floor 14) and n=2l+1 (floor 13); both floors least; ray carriers equal the #312 parity templates as exact affine tables; per-n witnesses re-derive every chosen child by the integral incidence identity, equal the complete graph vertex set and trace every seed to offset zero; corrupted children, a shifted occurrence, sub-floor witnesses and a third residue refuse; other gaps, class C and universal #139 open")
