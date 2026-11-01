"""R5 full stars, inherited exit and explicit source/image registry."""
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_r5_children import certify_r5_children, r5_image, r5_star_interface, r5_exit_interface


def main() raises:
    certify_r5_children()
    var candidate=enlarged_candidate(True)
    for w in candidate:
        print("CLASS_A_R5_CANDIDATE_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              r5_star_interface(w),r5_star_interface(w,True),r5_exit_interface(w))
    var image=r5_image()
    for w in image:
        print("CLASS_A_R5_IMAGE_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              r5_star_interface(w),r5_star_interface(w,True),r5_exit_interface(w))
