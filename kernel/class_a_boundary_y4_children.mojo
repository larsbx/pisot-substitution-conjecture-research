"""Replay Y4 complete stars, all-child tails, T2 exit and source/image flags."""
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_y4_children import certify_y4_children, y4_image, y4_star_interface, y4_exit_interface


def main() raises:
    certify_y4_children()
    var candidate=enlarged_candidate(True)
    for w in candidate:
        print("CLASS_A_Y4_CANDIDATE_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              y4_star_interface(w),y4_star_interface(w,True),
              y4_exit_interface(w),y4_exit_interface(w,True))
    var image=y4_image()
    for w in image:
        print("CLASS_A_Y4_IMAGE_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,
              y4_star_interface(w),y4_star_interface(w,True),
              y4_exit_interface(w),y4_exit_interface(w,True))
