"""Replay B4 stars, companion exits and separate source/image registries."""
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_b4_children import certify_b4_children, b4_image, b4_star_interface, b4_exit_interface


def main() raises:
    certify_b4_children()
    var candidate=enlarged_candidate(True)
    for w in candidate:
        print("CLASS_A_B4_CANDIDATE_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              b4_star_interface(w),b4_star_interface(w,True),
              b4_exit_interface(w),b4_exit_interface(w,True))
    var image=b4_image()
    for w in image:
        print("CLASS_A_B4_IMAGE_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              b4_star_interface(w),b4_star_interface(w,True),
              b4_exit_interface(w),b4_exit_interface(w,True))
