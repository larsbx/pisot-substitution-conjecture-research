"""Replay E6 complete stars, all-child tails and named interface reconciliation."""
from psc.class_a_boundary_e6_children import certify_e6_children, e6_image, e6_star_interface, e6_exit_interface
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_b5_children import b5_image
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,e6_star_interface(w),e6_star_interface(w,True),e6_exit_interface(w),e6_exit_interface(w,True))


def main() raises:
    certify_e6_children()
    emit("CLASS_A_E6_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_E6_IMAGE_REGISTRY",e6_image())
    emit("CLASS_A_E6_B5_IMAGE_REGISTRY",b5_image())
