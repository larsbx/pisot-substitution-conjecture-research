"""Replay E7 stars, uniform exits and separate star/exit interface rows."""
from psc.class_a_boundary_e7_children import certify_e7_children, e7_image, e7_star_interface, e7_exit_interface
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_b5_children import b5_image
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,e7_star_interface(w),e7_star_interface(w,True),e7_exit_interface(w),e7_exit_interface(w,True))


def main() raises:
    certify_e7_children()
    emit("CLASS_A_E7_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_E7_IMAGE_REGISTRY",e7_image())
    emit("CLASS_A_E7_B5_IMAGE_REGISTRY",b5_image())
