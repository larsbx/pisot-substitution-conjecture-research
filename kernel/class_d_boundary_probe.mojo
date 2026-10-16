"""Eight fixed all-seed exact graphs: s=+/-1, a=0..3, b=0; cap 20000 each.
Run: cd kernel && mojo run -I . class_d_boundary_probe.mojo
"""
from psc.class_d_boundary import boundary_probe, boundary_edge_flags


def main() raises:
    print("s a p q r states max_half_depth missing")
    var failures = 0
    var signs: List[Int] = [1, -1]
    for s in signs:
        for a in range(4):
            var row = boundary_probe(s, a)
            print(s, a, row[0], row[1], row[2], row[3], row[4], row[5])
            failures += row[5]
    var earlier = boundary_edge_flags(2)
    var later = boundary_edge_flags(3)
    print("s=-1,b=0: selected directed-edge flags at a=2:", earlier[0], earlier[1])
    print("s=-1,b=0: selected directed-edge flags at a=3:", later[0], later[1])
    print("domain=EIGHT_FIXED_MEMBERS; state_cap=20000; rng=NONE")
    if failures != 0:
        raise Error("FINITE_MEMBER_HAS_A_TARGET_FREE_VERTEX; no universal verdict")
    print("status=BOUNDED_CALIBRATION_COMPLETE; family_exhaustion=NOT_CLAIMED")
