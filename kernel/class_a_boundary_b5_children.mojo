"""Replay complete B5 stars, bounded all-child walks and source flags."""
from psc.class_a_boundary_b5_children import certify_b5_children, b5_image, b5_star_interface, b5_exit_interface
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,b5_star_interface(w),b5_star_interface(w,True),b5_exit_interface(w),b5_exit_interface(w,True))


def main() raises:
    certify_b5_children()
    emit("CLASS_A_B5_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_B5_IMAGE_REGISTRY",b5_image())
