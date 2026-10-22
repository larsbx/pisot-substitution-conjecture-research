"""Every seed and occurrence child, with no assumed sum bound on children."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract, require_claim
from psc.class_d_minus_seed_cover import verify_minus_seed_cover, seed_cover_check, strict_geometry_refuted, root_region
from psc.class_d_minus_spine_data import minus_spine_rows
from psc.class_d_positive_b_geometry import _margins20


def main() raises:
    var counts = verify_minus_seed_cover()
    assert_equal(counts[0],145)
    assert_equal(counts[1]+counts[2],12)
    assert_equal(counts[5],counts[6]+counts[7]+counts[8])
    # This alleged child fits the independent root box but violates the
    # correlated region. It is not an actual substitution counterexample.
    var forms = root_region(False)
    var control_rows: List[List[Int]] = [[0,1,0,0,-1],[2,2,-1,-1,1]]
    for row in control_rows:
        var ms = _margins20(row)
        forms.append(ms[0].copy())
        forms.append(ms[1].copy())
    assert_true(not strict_geometry_refuted(forms))
    forms.append([0,10,-7])
    forms.append([10,-10,-3])
    assert_true(strict_geometry_refuted(forms))
    # Equal-letter zero states are terminal; distinct-letter zeros still
    # contribute all nine segment pairs to the positive enumeration above.
    assert_equal(counts[4],9*(145-counts[3]))
    var rows = minus_spine_rows()
    var damaged = List[List[Int]]()
    for row in rows:
        if row[0] == 2 and row[1] == 2 and row[2] == 0 and row[3] == 0 and row[4] == 0:
            continue
        damaged.append(row.copy())
    var refused = False
    try:
        _ = seed_cover_check(damaged)
    except:
        refused = True
    assert_true(refused)  # a real child target was removed
    refused = False
    try:
        _ = seed_cover_check(rows,False)
    except:
        refused = True
    assert_true(refused)  # coarse box cannot certify seed inclusion
    require_contract("uniform minus class-D a>=2,b>=1: all 12 swap-seed candidates covered or exactly nonreal; every legal real child of a nonterminal real carrier state remains in the sealed 145-label sum<=1 carrier; no assumed child sum bound; exact correlated root region; coarse geometry and removed target refuse")
    require_claim("MinusClassDSeedCarrierClosure")
    require_claim("MinusClassDPositiveBCycleSum")
