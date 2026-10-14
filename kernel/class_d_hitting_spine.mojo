"""Replay finite common target spine; no all-parameter certificate."""
from psc.boundary_hitting_spine import minus_common_spine


def main() raises:
    var row = minus_common_spine()
    print("s=-1 b=0 a=2..8 vertices edges targets maximum_rank:", row)
    print("authority=canonical-Mojo; domain=SEVEN_FIXED_MEMBERS; family_exhaustion=NOT_CLAIMED")
