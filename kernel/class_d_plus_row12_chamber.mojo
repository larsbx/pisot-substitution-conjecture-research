"""Canonical receipt for the plus row-12 integer chamber squeeze."""
from psc.class_d_plus_row12_chamber import verify_plus_row12_integer_chamber


def main() raises:
    var out = verify_plus_row12_integer_chamber()
    print(
        "CLASS_D_PLUS_ROW12_INTEGER_CHAMBER_CERTIFIED",
        "inequalities=", out[0],
        "interface_b=", String(out[1]) + "*a+" + String(out[2]),
        "interface_c=", String(out[3]) + "*a+" + String(out[4]),
    )
