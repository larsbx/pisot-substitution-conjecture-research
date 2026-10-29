"""D0 complete stars, all-child tails and separate source/exit registry rows."""
from psc.class_a_boundary_d0_children import certify_d0_children, d0_source, d0_image, d0_star_interface, d0_exit_interface
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_e7_children import e7_image
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,d0_star_interface(w),d0_star_interface(w,True),d0_exit_interface(w),d0_exit_interface(w,True))


def main() raises:
    certify_d0_children()
    emit("CLASS_A_D0_SOURCE_REGISTRY",[d0_source(0),d0_source(1)])
    emit("CLASS_A_D0_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_D0_IMAGE_REGISTRY",d0_image())
    emit("CLASS_A_D0_E7_IMAGE_REGISTRY",e7_image())
