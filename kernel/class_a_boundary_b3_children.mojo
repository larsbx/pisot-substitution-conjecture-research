"""Replay complete B3 stars, two-edge exits and the 41-row source inventory."""
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_b3_children import certify_b3_children, b3_star_interface, b3_registered_exit


def main() raises:
    certify_b3_children()
    var labels=enlarged_candidate(True)
    for w in labels:
        print("CLASS_A_B3_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              b3_star_interface(w),b3_star_interface(w,True),
              1 if b3_registered_exit(w) else 0,
              1 if b3_registered_exit(w,True) else 0)
