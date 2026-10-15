"""Replay the HISTORICAL radius-eight example, as a bounded negative control.

Usage (repository root):
    cd kernel && mojo run -I . boxwalk_radius_probe.mojo

Fixed deterministic budget: depths 0..9, 30,000 symbols per side.
Each depth exhausts ALL aligned cuts of sigma^d(01) / sigma^d(10).
This is not a search over substitutions, nor a saturation certificate.
"""

from psc.boxwalk_radius_probe import historical_swap_probe


def main() raises:
    var rows = historical_swap_probe(9, 30000)
    print("sigma=001/22/220; seeds=01/10; max_depth=9; max_symbols_per_side=30000")
    print("depth length aligned_radius first_max_cut defect_at_first_max")
    for k in range(len(rows)):
        var r = rows[k]
        print(r.depth, r.word_length, r.radius, r.first_cut, r.d0, r.d1, r.d2)
    if rows[9].radius > 8:
        print("status=FINITE_COUNTEREXAMPLE_TO_ALIGNED_RADIUS_LE_8")
    else:
        raise Error("radius-eight regression failed")
    print("saturation=NOT_CHECKED; constrained_family_exhaustion=NOT_CHECKED")
