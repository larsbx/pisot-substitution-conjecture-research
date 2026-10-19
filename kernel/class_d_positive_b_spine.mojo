"""Canonical receipt for the positive-b minus class-D rank spine."""
from psc.class_d_positive_b_spine import verify_minus_positive_b_spine


def main() raises:
    var out = verify_minus_positive_b_spine()
    print(
        "CLASS_D_MINUS_POSITIVE_B_SPINE_CERTIFIED",
        "rows=", out[0],
        "targets=", out[1],
        "direct=", out[2],
        "alternate=", out[3],
        "special=", out[4],
        "max_rank=", out[5],
    )
