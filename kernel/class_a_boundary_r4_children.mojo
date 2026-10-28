"""Replay R4 stars, companion exits and separate source/image registries."""
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_r4_children import certify_r4_children, r4_image, r4_star_interface, r4_exit_interface


def main() raises:
    certify_r4_children()
    var candidate=enlarged_candidate(True)
    for w in candidate:
        print("CLASS_A_R4_CANDIDATE_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              r4_star_interface(w),r4_star_interface(w,True),
              r4_exit_interface(w),r4_exit_interface(w,True))
    var image=r4_image()
    for w in image:
        print("CLASS_A_R4_IMAGE_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              r4_star_interface(w),r4_star_interface(w,True),
              r4_exit_interface(w),r4_exit_interface(w,True))
