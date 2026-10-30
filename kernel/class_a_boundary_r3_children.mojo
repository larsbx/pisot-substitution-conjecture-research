"""Replay R3/D3 complete-star identities and scoped typed exits."""
from psc.class_a_boundary_r3_children import certify_r3_children, enlarged_candidate, star_interface, has_registered_exit

def main() raises:
    certify_r3_children()
    var labels=enlarged_candidate()
    for w in labels:
        print("CLASS_A_R3_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              star_interface(w),star_interface(w,True),
              1 if has_registered_exit(w) else 0,
              1 if has_registered_exit(w,True) else 0)
