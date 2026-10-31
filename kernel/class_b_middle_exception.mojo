"""The sole minus g=12 middle residue, certified with the existing ray engine."""
from psc.class_b_ray_line import BRay
from psc.class_b_ray_certificate import certify_ray_rows
from psc.class_b_middle_tables import middle_rows
from psc.class_b_middle_potential_tables import middle_potentials


def main() raises:
    _ = certify_ray_rows(BRay(-1, 12, 6), 54, middle_rows(-1), middle_potentials(-1))
    print("CLASS_B_MIDDLE_EXCEPTION minus g=12 r=6 l>=4 certified=true")
