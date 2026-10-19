"""Canonical receipt for conditional geometry of the minus positive-b spine."""
from psc.class_d_positive_b_geometry import verify_minus_positive_b_conditional_geometry


def main() raises:
    var out = verify_minus_positive_b_conditional_geometry()
    print(
        "CLASS_D_MINUS_POSITIVE_B_GEOMETRY_CERTIFIED",
        "rows=", out[0],
        "targets=", out[1],
        "cases=", out[2],
        "margin_implications=", out[3],
        "target_margin_gt=", String(out[4]) + "/" + String(out[5]),
    )
