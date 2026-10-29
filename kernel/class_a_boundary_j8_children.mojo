"""J8 complete stars, guarded tails and separate uniform interface flags."""
from psc.class_a_boundary_j8_children import certify_j8_children, j8_source, j8_image, j8_star_interface, j8_exit_interface
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_e7_children import e7_image
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,j8_star_interface(w),j8_star_interface(w,True),j8_exit_interface(w),j8_exit_interface(w,True))


def main() raises:
    certify_j8_children()
    var sources=List[BoundaryLabel]()
    for kind in range(28):sources.append(j8_source(kind))
    emit("CLASS_A_J8_SOURCE_REGISTRY",sources)
    emit("CLASS_A_J8_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_J8_IMAGE_REGISTRY",j8_image())
    emit("CLASS_A_J8_E7_IMAGE_REGISTRY",e7_image())
