"""Canonical conditional reduction for minus positive-b boundary hitting.

The only unproved premise is the cycle-sum lemma:
every genuine cyclic overlap has |wx+wc+wy| <= 1.
"""
from psc.class_d_minus_cycle_superset import verify_minus_cycle_superset
from psc.class_d_minus_exceptional_cycles import verify_minus_exceptional_productivity


def main() raises:
    var sup = verify_minus_cycle_superset()
    var exc = verify_minus_exceptional_productivity()
    print(
        "CLASS_D_MINUS_POSITIVE_B_CYCLE_REDUCTION_CERTIFIED",
        "states=", sup[0],
        "recurrent=", sup[1],
        "carrier=", sup[2],
        "zero=", sup[3],
        "boundary_only=", sup[4],
        "exceptional=", sup[5],
        "exceptional_edges=", exc[1],
        "open_premise=cycle_sum_abs_le_1",
    )
